export type CanonicalTerm =
  | { readonly node: "app"; readonly label: string; readonly args: readonly CanonicalTerm[] }
  | { readonly node: "token"; readonly sort: string; readonly value: string }
  | { readonly node: "variable"; readonly name: string; readonly sort?: string };

type Json = Record<string, any>;

export function canonicalTerm(term: Json): CanonicalTerm {
  switch (term?.node) {
    case "KApply": {
      const label = term.label?.name;
      if (typeof label !== "string") throw new Error("KApply without a label");
      const cast = /^#SemanticCastTo(.+)$/.exec(label);
      if (cast !== null && term.args.length === 1 && term.args[0]?.node === "KVariable") {
        return { node: "variable", name: term.args[0].name, sort: cast[1]! };
      }
      return { node: "app", label, args: term.args.map(canonicalTerm) };
    }
    case "KToken": return { node: "token", sort: term.sort.name, value: term.token };
    case "KVariable": {
      const sort = term.sort?.name;
      return sort === undefined
        ? { node: "variable", name: term.name }
        : { node: "variable", name: term.name, sort };
    }
    case "KRewrite": return { node: "app", label: "#KRewrite", args: [canonicalTerm(term.lhs), canonicalTerm(term.rhs)] };
    default: throw new Error(`Unsupported KAST node ${term?.node ?? typeof term}`);
  }
}

export const app = (label: string, ...args: CanonicalTerm[]): CanonicalTerm => ({ node: "app", label, args });
export const token = (sort: string, value: string): CanonicalTerm => ({ node: "token", sort, value });

export function extractLabelledRule(parsed: Json, label: string): CanonicalTerm {
  for (const module of parsed.term.modules) {
    for (const sentence of module.localSentences) {
      if (sentence.node === "KRule" && sentence.att?.att?.label === label) return canonicalTerm(sentence.body);
    }
  }
  throw new Error(`No parsed rule labelled ${label}`);
}
