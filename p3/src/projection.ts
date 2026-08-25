import {
  ATT_LABEL,
  attString,
  classifyAxiom,
  parseDefinition,
} from "../../../k-framework-ts/packages/kore/dist/index.js";

type Json = Record<string, any>;

export interface Edge { readonly child: string; readonly parent: string }
export type Fact =
  | { readonly kind: "context"; readonly label: string; readonly phase: "heat" | "cool"; readonly cells: readonly string[] }
  | { readonly kind: "rule"; readonly label: string; readonly mode: string; readonly cells: readonly string[]; readonly requires: boolean; readonly ensures: boolean }
  | { readonly kind: "function-injection"; readonly label: string; readonly function: string };
export interface Projection { readonly edges: readonly Edge[]; readonly facts: readonly Fact[] }

const baseLabel = (node: Json): string => String(node.label?.name ?? "").split("(", 1)[0]!;
const stringToken = (node: Json): string => JSON.parse(node.token);
const key = (value: unknown): string => JSON.stringify(value);
const sortedCells = (cells: Iterable<string>): string[] => [...new Set(cells)].toSorted();

export function normalizeProjection(projection: Projection): Projection {
  const facts = projection.facts.map((fact): Fact =>
    "cells" in fact ? { ...fact, cells: sortedCells(fact.cells) } : fact,
  ).toSorted((a, b) => key(a).localeCompare(key(b)));
  return {
    edges: projection.edges.toSorted((a, b) => key(a).localeCompare(key(b))),
    facts,
  };
}

function findCell(node: Json, label: string): Json | undefined {
  if (node?.node === "KApply" && node.label?.name === label) return node.args[0];
  for (const child of node?.args ?? []) {
    const found = findCell(child, label);
    if (found !== undefined) return found;
  }
  return undefined;
}

function decodeList<T>(node: Json, cons: string, nil: string, decode: (node: Json) => T): T[] {
  const result: T[] = [];
  let cursor = node;
  while (baseLabel(cursor) === cons) {
    result.push(decode(cursor.args[0]));
    cursor = cursor.args[1];
  }
  if (baseLabel(cursor) !== nil) throw new Error(`Malformed ${cons} list`);
  return result;
}

const decodeCells = (node: Json): string[] => decodeList(node, "pCellCons", "pCellNil", stringToken);

export function decodeP3Result(document: Json): { readonly term: Json; readonly projection: Projection } {
  const sequence = findCell(document.term, "<p3Result>");
  if (sequence?.node !== "KSequence" || sequence.items.length !== 1) throw new Error("Malformed <p3Result>");
  const term = sequence.items[0];
  if (baseLabel(term) !== "p3Projection") throw new Error("P3 did not produce a projection");
  const edges = decodeList(term.args[0], "pCellEdgeCons", "pCellEdgeNil", (edge): Edge => ({
    child: stringToken(edge.args[0]), parent: stringToken(edge.args[1]),
  }));
  const facts = decodeList(term.args[1], "pFactCons", "pFactNil", (fact): Fact => {
    switch (baseLabel(fact)) {
      case "pContextRule": return {
        kind: "context", label: stringToken(fact.args[0]), phase: stringToken(fact.args[1]) as "heat" | "cool",
        cells: decodeCells(fact.args[2]),
      };
      case "pConcretizedRule": return {
        kind: "rule", label: stringToken(fact.args[0]), mode: stringToken(fact.args[1]), cells: decodeCells(fact.args[2]),
        requires: stringToken(fact.args[3]) === "true", ensures: stringToken(fact.args[4]) === "true",
      };
      case "pFunctionInjection": return {
        kind: "function-injection", label: stringToken(fact.args[0]), function: stringToken(fact.args[1]),
      };
      default: throw new Error(`Unknown P3 fact ${baseLabel(fact)}`);
    }
  });
  return { term, projection: normalizeProjection({ edges, facts }) };
}

function visit(value: unknown, action: (node: Json) => void): void {
  if (value === null || typeof value !== "object") return;
  if (Array.isArray(value)) {
    for (const child of value) visit(child, action);
    return;
  }
  const node = value as Json;
  action(node);
  for (const child of Object.values(node)) visit(child, action);
}

const cellNames = (body: Json): string[] => {
  const cells = new Set<string>();
  visit(body, (node) => {
    if (node.node !== "KApply") return;
    const match = /^<(.+)>$/.exec(node.label?.name ?? "");
    if (match !== null && match[1] !== "generatedCounter") cells.add(match[1]!);
  });
  return sortedCells(cells);
};

const nontrivial = (term: Json): boolean =>
  !(term?.node === "KToken" && term.sort?.name === "Bool" && term.token === "true");

const contextLabels = new Map<string, "heat" | "cool">([
  ["P3-COUPLED-SYNTAX.add1-heat", "heat"],
  ["P3-COUPLED-SYNTAX.add1-cool", "cool"],
  ["P3-COUPLED-SYNTAX.add2-heat", "heat"],
  ["P3-COUPLED-SYNTAX.add2-cool", "cool"],
  ["P3-COUPLED.hold-context-heat", "heat"],
  ["P3-COUPLED.hold-context-cool", "cool"],
]);
const sourceModes = new Map([
  ["read-state", "function-context"],
  ["bump-state", "rewrite"],
  ["add-values", "rewrite"],
  ["hold-value", "rewrite"],
  ["start-program", "rewrite"],
]);

export function projectCompiled(document: Json, fixturePath: string): Projection {
  const module = document.term.modules.find((item: Json) => item.name === "P3-COUPLED");
  if (module === undefined) throw new Error("P3-COUPLED module missing");
  const productions: Json[] = module.localSentences.filter((item: Json) => item.node === "KProduction");
  const sourceCells = productions.filter((item) =>
    item.att?.att?.cell !== undefined && item.att?.att?.["org.kframework.attributes.Source"] === fixturePath,
  );
  const selectedCells = [...sourceCells, ...productions.filter((item) => item.klabel?.name === "<generatedTop>")];
  const bySort = new Map(selectedCells.map((item) => [item.sort.name, item.att.att.cellName as string]));
  const edges: Edge[] = [];
  for (const parent of selectedCells) {
    for (const item of parent.productionItems) {
      if (item.node !== "KNonTerminal") continue;
      const child = bySort.get(item.sort.name);
      if (child !== undefined) edges.push({ child, parent: parent.att.att.cellName });
    }
  }

  const facts: Fact[] = [];
  for (const sentence of module.localSentences) {
    if (sentence.node !== "KRule") continue;
    const label = sentence.att?.att?.label;
    if (typeof label !== "string") continue;
    const phase = contextLabels.get(label);
    if (phase !== undefined) facts.push({ kind: "context", label, phase, cells: cellNames(sentence.body) });
    const mode = sourceModes.get(label);
    if (mode !== undefined) facts.push({
      kind: "rule", label, mode, cells: cellNames(sentence.body),
      requires: nontrivial(sentence.requires), ensures: nontrivial(sentence.ensures),
    });
  }

  const start = module.localSentences.find((sentence: Json) => sentence.node === "KRule" && sentence.att?.att?.label === "start-program");
  let injected = false;
  visit(start?.body, (node) => {
    if (node.node === "KApply" && node.label?.name === "read" && node.args?.length === 1) injected = true;
  });
  if (injected) facts.push({ kind: "function-injection", label: "start-program", function: "read" });
  return normalizeProjection({ edges, facts });
}

export function selectedKoreAxioms(text: string): readonly { readonly label: string; readonly kind: string }[] {
  const selected = new Set([...contextLabels.keys(), ...sourceModes.keys()]);
  const definition = parseDefinition(text);
  const result: { label: string; kind: string }[] = [];
  for (const sentence of definition.modules.flatMap((module) => module.sentences)) {
    if (sentence.tag !== "Axiom") continue;
    const label = attString(sentence.attrs, ATT_LABEL);
    if (label !== undefined && selected.has(label)) result.push({ label, kind: classifyAxiom(sentence).kind });
  }
  return result.toSorted((a, b) => a.label.localeCompare(b.label));
}

export function projectExecution(document: Json): { readonly k: string; readonly state: string } {
  const kCell = findCell(document.term, "<k>");
  const stateCell = findCell(document.term, "<state>");
  const kItem = kCell?.node === "KSequence" ? kCell.items[0] : undefined;
  if (kItem?.node !== "KToken" || stateCell?.node !== "KToken") throw new Error("Unexpected P3 execution result");
  return { k: kItem.token, state: stateCell.token };
}

export function renderKast(node: Json): string {
  if (node.node === "KToken") return node.token;
  if (node.node === "KApply") {
    const label = baseLabel(node);
    return node.args.length === 0 ? label : `${label}(${node.args.map(renderKast).join(", ")})`;
  }
  throw new Error(`Cannot render ${node.node}`);
}
