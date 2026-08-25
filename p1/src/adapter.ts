import { readFile } from "node:fs/promises";
import { resolve } from "node:path";
import type { PDefinition, PProduction, PRule, PTerm } from "./types.js";
import { trueTerm } from "./types.js";

type Json = Record<string, any>;

const att = (sentence: Json): Record<string, any> => sentence.att?.att ?? {};
const sourceOf = (sentence: Json): string | undefined => att(sentence)["org.kframework.attributes.Source"];

function sortName(sort: Json | undefined): string | undefined {
  return sort?.node === "KSort" ? sort.name : undefined;
}

function productionOf(sentence: Json): PProduction {
  const attributes = att(sentence);
  const label = sentence.klabel?.name ?? attributes.symbol;
  if (typeof label !== "string") throw new Error("P1 only accepts labelled productions");
  const result = sortName(sentence.sort);
  if (result === undefined) throw new Error(`Production ${label} has no concrete result sort`);
  const args = sentence.productionItems
    .filter((item: Json) => item.node === "KNonTerminal")
    .map((item: Json) => sortName(item.sort));
  if (args.some((item: string | undefined) => item === undefined)) {
    throw new Error(`Production ${label} has a parametric argument sort`);
  }
  return {
    label,
    sort: result,
    args: args as string[],
    kind: Object.hasOwn(attributes, "function") ? "function" : "constructor",
  };
}

function collectVariableSorts(node: Json | undefined, into: Map<string, string>): void {
  if (node === undefined || node === null || typeof node !== "object") return;
  if (node.node === "KApply" && /^#SemanticCastTo/.test(node.label?.name) && node.args?.length === 1) {
    const sort = String(node.label.name).slice("#SemanticCastTo".length);
    const child = node.args[0];
    if (child?.node === "KVariable") into.set(child.name, sort);
  }
  if (node.node === "KVariable") {
    const sort = sortName(node.sort);
    if (sort !== undefined) into.set(node.name, sort);
  }
  for (const child of Object.values(node)) {
    if (Array.isArray(child)) for (const item of child) collectVariableSorts(item, into);
    else if (child !== node) collectVariableSorts(child as Json, into);
  }
}

function termOf(
  node: Json,
  variables: ReadonlyMap<string, string>,
  productions: ReadonlyMap<string, PProduction>,
  expectedSort?: string,
): PTerm {
  switch (node?.node) {
    case "KVariable": {
      const sort = sortName(node.sort) ?? variables.get(node.name) ?? expectedSort;
      if (sort === undefined) throw new Error(`Cannot infer sort of variable ${node.name}`);
      return { kind: "var", name: node.name, sort };
    }
    case "KToken": {
      const sort = sortName(node.sort);
      if (sort === undefined) throw new Error("Token has no concrete sort");
      return { kind: "token", sort, value: node.token };
    }
    case "KApply": {
      const label = node.label?.name;
      if (typeof label !== "string") throw new Error("Application has no label");
      const cast = /^#SemanticCastTo(.+)$/.exec(label);
      if (cast !== null && node.args.length === 1) {
        return termOf(node.args[0], variables, productions, cast[1]);
      }
      const production = productions.get(label);
      return {
        kind: "app",
        label,
        args: node.args.map((child: Json, index: number) =>
          termOf(child, variables, productions, production?.args[index]),
        ),
      };
    }
    default:
      throw new Error(`P1 does not support parsed KAST node ${node?.node ?? typeof node}`);
  }
}

export async function adaptParsedDefinition(
  parsedPath: string,
  sourcePath: string,
  moduleName: string,
): Promise<PDefinition> {
  const document = JSON.parse(await readFile(parsedPath, "utf8"));
  const definition = document.term;
  const expectedSource = resolve(sourcePath);
  const modules: Json[] = definition.modules;
  const sourceModules = modules.filter((module) =>
    module.name === moduleName || module.name === `${moduleName}-SYNTAX`,
  );
  const sourceSentences = sourceModules.flatMap((module) => module.localSentences)
    .filter((sentence: Json) => sourceOf(sentence) === expectedSource);
  const productions = sourceModules
    .filter((module) => module.name === `${moduleName}-SYNTAX`)
    .flatMap((module) => module.localSentences)
    .filter((sentence: Json) => sentence.node === "KProduction" && sourceOf(sentence) === expectedSource)
    .map(productionOf);
  const productionMap = new Map(productions.map((production) => [production.label, production]));
  const rules: PRule[] = [];

  for (const sentence of sourceSentences.filter((item: Json) => item.node === "KRule")) {
    if (sentence.body?.node !== "KRewrite") throw new Error("P1 probe expects rewrite-bodied rules");
    const variables = new Map<string, string>();
    collectVariableSorts(sentence, variables);
    const lhs = termOf(sentence.body.lhs, variables, productionMap);
    const head = lhs.kind === "app" ? productionMap.get(lhs.label) : undefined;
    rules.push({
      kind: head?.kind === "function" ? "equation" : "rewrite",
      lhs,
      rhs: termOf(sentence.body.rhs, variables, productionMap, head?.sort),
      requires: sentence.requires === undefined ? trueTerm : termOf(sentence.requires, variables, productionMap, "Bool"),
      ensures: sentence.ensures === undefined ? trueTerm : termOf(sentence.ensures, variables, productionMap, "Bool"),
    });
  }

  const sorts = new Set<string>();
  for (const production of productions) {
    sorts.add(production.sort);
    for (const sort of production.args) sorts.add(sort);
  }
  return { module: moduleName, sorts: [...sorts].toSorted(), productions, rules };
}

const q = (value: string): string => JSON.stringify(value);
const list = <T>(values: readonly T[], cons: string, nil: string, render: (value: T) => string): string =>
  values.reduceRight((tail, value) => `${cons}(${render(value)}, ${tail})`, nil);

export function renderPTerm(term: PTerm): string {
  switch (term.kind) {
    case "var": return `pVar(${q(term.name)}, ${q(term.sort)})`;
    case "token": return `pToken(${q(term.sort)}, ${q(term.value)})`;
    case "app": return `pApp(${q(term.label)}, ${list(term.args, "pTermCons", "pTermNil", renderPTerm)})`;
  }
}

export function renderPDefinition(definition: PDefinition): string {
  const sorts = list(definition.sorts, "pSortCons", "pSortNil", (sort) => `pSort(${q(sort)})`);
  const productions = list(definition.productions, "pProductionCons", "pProductionNil", (production) => {
    const ctor = production.kind === "function" ? "pFunction" : "pConstructor";
    const args = list(production.args, "pSortCons", "pSortNil", (sort) => `pSort(${q(sort)})`);
    return `${ctor}(${q(production.label)}, ${q(production.sort)}, ${args})`;
  });
  const rules = list(definition.rules, "pRuleCons", "pRuleNil", (rule) => {
    const ctor = rule.kind === "equation" ? "pEquation" : "pRewrite";
    return `${ctor}(${renderPTerm(rule.lhs)}, ${renderPTerm(rule.rhs)}, ${renderPTerm(rule.requires)}, ${renderPTerm(rule.ensures)})`;
  });
  return `pDefinition(${q(definition.module)}, ${sorts}, ${productions}, ${rules})\n`;
}
