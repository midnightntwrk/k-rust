import { readFile } from "node:fs/promises";
import { resolve } from "node:path";
import {
  ATT_FUNCTION,
  attSource,
  classifyAxiom,
  demangleLabel,
  demangleSort,
  demangleVar,
  hasAtt,
  parseDefinition,
  type Pattern,
  type Sort,
} from "../../../k-framework-ts/packages/kore/dist/index.js";
import type { CanonicalAxiom, CanonicalProjection, PDefinition, PProduction, PTerm } from "./types.js";
import { normalizeProjection, trueTerm } from "./types.js";

const sourceSort = (sort: Sort): string => {
  if (sort.tag !== "SortApp") throw new Error(`P1 does not accept sort variable ${sort.name}`);
  return demangleSort(sort.name) ?? sort.name;
};

function children(pattern: Pattern): readonly Pattern[] {
  switch (pattern.tag) {
    case "App":
    case "LeftAssoc":
    case "RightAssoc": return pattern.args;
    case "And":
    case "Or":
    case "MultiOr": return pattern.patterns;
    case "Not":
    case "Next":
    case "Exists":
    case "Forall":
    case "Mu":
    case "Nu":
    case "Ceil":
    case "Floor": return [pattern.pattern];
    case "Implies":
    case "Iff":
    case "Equals":
    case "In":
    case "Rewrites": return [pattern.left, pattern.right];
    default: return [];
  }
}

function userApps(pattern: Pattern, labels: ReadonlySet<string>, into: string[] = []): string[] {
  if (pattern.tag === "App") {
    const label = demangleLabel(pattern.symbol);
    if (label !== undefined && labels.has(label)) into.push(label);
  }
  for (const child of children(pattern)) userApps(child, labels, into);
  return into;
}

function termOf(pattern: Pattern, labels: ReadonlySet<string>): PTerm {
  switch (pattern.tag) {
    case "EVar": return {
      kind: "var",
      name: demangleVar(pattern.name) ?? pattern.name.replace(/^Var/, ""),
      sort: sourceSort(pattern.sort),
    };
    case "DV": return { kind: "token", sort: sourceSort(pattern.sort), value: pattern.value.value };
    case "Top": return trueTerm;
    case "App": {
      if (pattern.symbol === "inj" && pattern.args.length === 1) return termOf(pattern.args[0]!, labels);
      if (pattern.symbol === "kseq" && pattern.args.length === 2
        && pattern.args[1]?.tag === "App" && pattern.args[1].symbol === "dotk") {
        return termOf(pattern.args[0]!, labels);
      }
      const label = demangleLabel(pattern.symbol);
      if (label === undefined) throw new Error(`P1 cannot demangle Kore symbol ${pattern.symbol}`);
      return { kind: "app", label, args: pattern.args.map((arg) => termOf(arg, labels)) };
    }
    default: throw new Error(`P1 projection cannot convert Kore ${pattern.tag} into a source term`);
  }
}

const pairKey = (labels: readonly string[]): string => labels.toSorted().join("\u0000");

export async function projectOfficialKore(
  definitionPath: string,
  sourcePath: string,
  expected: PDefinition,
): Promise<CanonicalProjection> {
  const definition = parseDefinition(await readFile(definitionPath, "utf8"));
  const expectedSource = resolve(sourcePath);
  const sentences = definition.modules.flatMap((module) => module.sentences);
  const expectedLabels = new Set(expected.productions.map((production) => production.label));
  const sourceSymbols = sentences.filter((sentence) =>
    sentence.tag === "SymbolDecl" && attSource(sentence.attrs) === expectedSource,
  );
  const symbols: PProduction[] = sourceSymbols.map((sentence): PProduction => {
    if (sentence.tag !== "SymbolDecl") throw new Error("unreachable");
    const label = demangleLabel(sentence.symbol.name);
    if (label === undefined) throw new Error(`Cannot demangle ${sentence.symbol.name}`);
    return {
      label,
      sort: sourceSort(sentence.sort),
      args: sentence.paramSorts.map(sourceSort),
      kind: hasAtt(sentence.attrs, ATT_FUNCTION) ? "function" : "constructor",
    };
  }).filter((symbol) => expectedLabels.has(symbol.label));
  const labels = new Set(symbols.map((symbol) => symbol.label));
  const constructors = new Map(symbols.filter((symbol) => symbol.kind === "constructor").map((symbol) => [symbol.label, symbol]));
  const axioms: CanonicalAxiom[] = [];
  const seen = new Set<string>();

  for (const sentence of sentences) {
    if (sentence.tag !== "Axiom") continue;
    const classified = classifyAxiom(sentence);
    const apps = [...new Set(userApps(sentence.pattern, labels))];
    if (apps.length === 0 && !(classified.kind === "equation" && labels.has(classified.symbol))) continue;
    let axiom: CanonicalAxiom | undefined;
    switch (classified.kind) {
      case "functional": {
        const label = apps.find((item) => constructors.has(item));
        if (label !== undefined) axiom = { kind: "functional", label };
        break;
      }
      case "no-confusion": {
        const ctorLabels = apps.filter((item) => constructors.has(item));
        const distinct = [...new Set(ctorLabels)];
        if (distinct.length === 1) axiom = { kind: "no-confusion-same", label: distinct[0]! };
        else if (distinct.length === 2) axiom = { kind: "no-confusion-different", labels: distinct.toSorted() };
        break;
      }
      case "no-junk": {
        const ctorLabels = apps.filter((item) => constructors.has(item)).toSorted();
        const sort = ctorLabels.length === 0 ? undefined : constructors.get(ctorLabels[0]!)?.sort;
        if (sort !== undefined) axiom = { kind: "no-junk", sort, labels: [...new Set(ctorLabels)] };
        break;
      }
      case "equation":
      case "owise":
      case "anywhere": {
        const label = demangleLabel(classified.symbol);
        if (label === undefined || !labels.has(label)) break;
        axiom = {
          kind: "equation",
          lhs: termOf(classified.lhs, labels),
          rhs: termOf(classified.rhs, labels),
          requires: classified.requires === undefined ? trueTerm : termOf(classified.requires, labels),
          ensures: classified.ensures === undefined ? trueTerm : termOf(classified.ensures, labels),
        };
        break;
      }
    }
    if (axiom !== undefined) {
      const key = axiom.kind === "no-confusion-different" ? `${axiom.kind}:${pairKey(axiom.labels)}` : JSON.stringify(axiom);
      if (!seen.has(key)) {
        seen.add(key);
        axioms.push(axiom);
      }
    }
  }

  return normalizeProjection({
    module: expected.module,
    sorts: expected.sorts,
    symbols,
    axioms,
  });
}
