export type PTerm =
  | { readonly kind: "var"; readonly name: string; readonly sort: string }
  | { readonly kind: "app"; readonly label: string; readonly args: readonly PTerm[] }
  | { readonly kind: "token"; readonly sort: string; readonly value: string };

export interface PProduction {
  readonly label: string;
  readonly sort: string;
  readonly args: readonly string[];
  readonly kind: "constructor" | "function";
}

export interface PRule {
  readonly kind: "equation" | "rewrite";
  readonly lhs: PTerm;
  readonly rhs: PTerm;
  readonly requires: PTerm;
  readonly ensures: PTerm;
}

export interface PDefinition {
  readonly module: string;
  readonly sorts: readonly string[];
  readonly productions: readonly PProduction[];
  readonly rules: readonly PRule[];
}

export type CanonicalAxiom =
  | { readonly kind: "functional"; readonly label: string }
  | { readonly kind: "no-confusion-same"; readonly label: string }
  | { readonly kind: "no-confusion-different"; readonly labels: readonly string[] }
  | { readonly kind: "no-junk"; readonly sort: string; readonly labels: readonly string[] }
  | ({ readonly kind: "equation" | "rewrite" } & Omit<PRule, "kind">);

export interface CanonicalProjection {
  readonly module: string;
  readonly sorts: readonly string[];
  readonly symbols: readonly PProduction[];
  readonly axioms: readonly CanonicalAxiom[];
}

export const trueTerm: PTerm = { kind: "token", sort: "Bool", value: "true" };

export function stable<T>(value: T): T {
  if (Array.isArray(value)) return value.map(stable) as T;
  if (value !== null && typeof value === "object") {
    return Object.fromEntries(
      Object.entries(value as Record<string, unknown>)
        .toSorted(([a], [b]) => a.localeCompare(b))
        .map(([key, child]) => [key, stable(child)]),
    ) as T;
  }
  return value;
}

export const keyOf = (value: unknown): string => JSON.stringify(stable(value));

export function normalizeProjection(value: CanonicalProjection): CanonicalProjection {
  return {
    module: value.module,
    sorts: value.sorts.toSorted(),
    symbols: value.symbols.toSorted((a, b) => keyOf(a).localeCompare(keyOf(b))),
    axioms: value.axioms.toSorted((a, b) => keyOf(a).localeCompare(keyOf(b))),
  };
}
