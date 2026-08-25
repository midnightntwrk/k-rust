import { mkdir, readFile, realpath, stat, writeFile } from "node:fs/promises";
import { dirname, resolve } from "node:path";

export async function pathExists(path: string): Promise<boolean> {
  try {
    await stat(path);
    return true;
  } catch (error) {
    if (isNodeError(error) && error.code === "ENOENT") return false;
    throw error;
  }
}

export function isNodeError(error: unknown): error is NodeJS.ErrnoException {
  return error instanceof Error && "code" in error;
}

export async function readJson(path: string): Promise<unknown> {
  const text = await readFile(path, "utf8");
  try {
    return JSON.parse(text) as unknown;
  } catch (error) {
    throw new Error(`Invalid JSON in ${path}: ${error instanceof Error ? error.message : String(error)}`);
  }
}

export async function writeJson(path: string, value: unknown): Promise<void> {
  await mkdir(dirname(path), { recursive: true });
  await writeFile(path, `${JSON.stringify(value, null, 2)}\n`, "utf8");
}

export async function sha256File(path: string): Promise<string> {
  return sha256(await readFile(path));
}

export function sha256(value: string | Uint8Array): string {
  return new Bun.CryptoHasher("sha256").update(value).digest("hex");
}

export async function resolveExecutable(command: string): Promise<{ invoked: string; resolved: string }> {
  const found = command.includes("/") ? resolve(command) : Bun.which(command);
  if (found === null) throw new Error(`Executable not found: ${command}`);
  return { invoked: found, resolved: await realpath(found) };
}

export function requireObject(value: unknown, where: string): Record<string, unknown> {
  if (typeof value !== "object" || value === null || Array.isArray(value)) {
    throw new Error(`${where} must be an object`);
  }
  return value as Record<string, unknown>;
}

export function requireString(value: unknown, where: string): string {
  if (typeof value !== "string" || value.length === 0) throw new Error(`${where} must be a non-empty string`);
  return value;
}

export function requireBoolean(value: unknown, where: string): boolean {
  if (typeof value !== "boolean") throw new Error(`${where} must be a boolean`);
  return value;
}

export function requireStringArray(value: unknown, where: string): readonly string[] {
  if (!Array.isArray(value) || value.some((item) => typeof item !== "string" || item.length === 0)) {
    throw new Error(`${where} must be an array of non-empty strings`);
  }
  return value as string[];
}

export function requireNumberArray(value: unknown, where: string): readonly number[] {
  if (!Array.isArray(value) || value.length === 0 || value.some((item) => !Number.isInteger(item))) {
    throw new Error(`${where} must be a non-empty array of integer exit codes`);
  }
  return value as number[];
}
