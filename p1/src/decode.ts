import { readFile } from "node:fs/promises";
import type { CanonicalAxiom, CanonicalProjection, PProduction, PTerm } from "./types.js";
import { normalizeProjection } from "./types.js";

type Json = Record<string, any>;

const labelOf = (node: Json): string => String(node.label?.name ?? "").split("(", 1)[0]!;
const stringOf = (node: Json): string => {
  if (node.node !== "KToken" || node.sort?.name !== "String") throw new Error("Expected a K String token");
  return JSON.parse(node.token);
};

function findCell(node: Json, label: string): Json | undefined {
  if (node?.node === "KApply" && node.label?.name === label) return node.args[0];
  for (const arg of node?.args ?? []) {
    const found = findCell(arg, label);
    if (found !== undefined) return found;
  }
  return undefined;
}

export function resultTerm(document: Json): Json {
  const cell = findCell(document.term, "<result>");
  if (cell?.node !== "KSequence" || cell.items.length !== 1) {
    throw new Error("Expected <result> to contain exactly one K item");
  }
  return cell.items[0];
}

function decodeList<T>(node: Json, cons: string, nil: string, decode: (item: Json) => T): T[] {
  const values: T[] = [];
  let cursor = node;
  while (labelOf(cursor) === cons) {
    values.push(decode(cursor.args[0]));
    cursor = cursor.args[1];
  }
  if (labelOf(cursor) !== nil) throw new Error(`Malformed ${cons} list: ended at ${labelOf(cursor)}`);
  return values;
}

function termOf(node: Json): PTerm {
  switch (labelOf(node)) {
    case "pVar": return { kind: "var", name: stringOf(node.args[0]), sort: stringOf(node.args[1]) };
    case "pToken": return { kind: "token", sort: stringOf(node.args[0]), value: stringOf(node.args[1]) };
    case "pApp": return {
      kind: "app",
      label: stringOf(node.args[0]),
      args: decodeList(node.args[1], "pTermCons", "pTermNil", termOf),
    };
    default: throw new Error(`Not a PTerm: ${labelOf(node)}`);
  }
}

export function decodeKoreModule(node: Json): CanonicalProjection {
  if (labelOf(node) !== "koreModule") throw new Error(`Expected koreModule, got ${labelOf(node)}`);
  const module = stringOf(node.args[0]);
  const sorts = decodeList(node.args[1], "koreSortCons", "koreSortNil", (sort) => {
    if (labelOf(sort) !== "koreSort") throw new Error("Malformed sort declaration");
    return stringOf(sort.args[0]);
  });
  const symbols: PProduction[] = decodeList(node.args[2], "koreSymbolCons", "koreSymbolNil", (symbol) => {
    if (labelOf(symbol) !== "koreSymbol") throw new Error("Malformed symbol declaration");
    const attrs = labelOf(symbol.args[3]);
    return {
      label: stringOf(symbol.args[0]),
      sort: stringOf(symbol.args[1]),
      args: decodeList(symbol.args[2], "pSortCons", "pSortNil", (sort) => stringOf(sort.args[0])),
      kind: attrs === "koreFunctionAttrs" ? "function" : "constructor",
    };
  });
  const axioms: CanonicalAxiom[] = decodeList(node.args[3], "koreAxiomCons", "koreAxiomNil", (axiom) => {
    const label = labelOf(axiom);
    switch (label) {
      case "koreFunctional": return { kind: "functional", label: stringOf(axiom.args[0]) };
      case "koreNoConfusionSame": return { kind: "no-confusion-same", label: stringOf(axiom.args[0]) };
      case "koreNoConfusionDifferent": return {
        kind: "no-confusion-different",
        labels: [stringOf(axiom.args[0]), stringOf(axiom.args[1])].toSorted(),
      };
      case "koreNoJunk": return {
        kind: "no-junk",
        sort: stringOf(axiom.args[0]),
        labels: decodeList(axiom.args[1], "pLabelCons", "pLabelNil", stringOf).toSorted(),
      };
      case "koreEquation":
      case "koreRewrite": return {
        kind: label === "koreEquation" ? "equation" : "rewrite",
        lhs: termOf(axiom.args[0]),
        rhs: termOf(axiom.args[1]),
        requires: termOf(axiom.args[2]),
        ensures: termOf(axiom.args[3]),
      };
      default: throw new Error(`Unknown P1 axiom ${label}`);
    }
  });
  return normalizeProjection({ module, sorts, symbols, axioms });
}

export async function decodeKrunResult(path: string): Promise<{ readonly term: Json; readonly projection: CanonicalProjection }> {
  const document = JSON.parse(await readFile(path, "utf8"));
  const term = resultTerm(document);
  return { term, projection: decodeKoreModule(term) };
}

export function renderKast(node: Json): string {
  switch (node.node) {
    case "KToken": return node.token;
    case "KApply": {
      const label = labelOf(node);
      return node.args.length === 0 ? label : `${label}(${node.args.map(renderKast).join(", ")})`;
    }
    default: throw new Error(`Cannot render fixed-point KAST node ${node.node}`);
  }
}
