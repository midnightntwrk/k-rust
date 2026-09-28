#!/usr/bin/env python3
"""Build one KORE JSON-RPC request from a krust state via kore-parser."""

import argparse
import os
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--krust", required=True)
    parser.add_argument("--definition", required=True)
    parser.add_argument("--module", required=True)
    parser.add_argument("--sort", required=True)
    parser.add_argument("--program-file", required=True)
    parser.add_argument("--config", action="append", default=[])
    parser.add_argument("--state-depth", type=int)
    parser.add_argument("--method", choices=("execute", "simplify"), required=True)
    parser.add_argument("--max-depth", type=int, default=2)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()

    kompile = Path(os.environ["K_KOMPILE"])
    kore_parser = kompile.with_name("kore-parser")
    definition = Path(args.definition)
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)

    with tempfile.TemporaryDirectory(dir=output.parent) as temporary:
        state_kore = Path(temporary) / "state.kore"
        state_json = Path(temporary) / "state.json"
        command = [args.krust, "krun", "--definition", str(definition),
                   "--sort", args.sort, "--io", "off"]
        for config in args.config:
            command.extend(("-c", config))
        if args.state_depth is not None:
            command.extend(("--depth", str(args.state_depth)))
        command.append(args.program_file)
        with state_kore.open("wb") as writer:
            subprocess.run(command, stdin=subprocess.DEVNULL, stdout=writer, check=True)
        with state_json.open("wb") as writer:
            # This is a syntax conversion. Some krust-generated definitions contain
            # equations the reference verifier rejects even though their patterns parse.
            subprocess.run([str(kore_parser), str(definition / "definition.kore"),
                            "--pattern", str(state_kore), "--module", args.module,
                            "--print-pattern-json", "--no-print-definition", "--no-verify"],
                           stdin=subprocess.DEVNULL, stdout=writer, check=True)

        with output.open("wb") as writer, state_json.open("rb") as reader:
            writer.write(b'{"jsonrpc":"2.0","id":1,"method":"' + args.method.encode()
                         + b'","params":{"state":')
            while chunk := reader.read(1 << 20):
                writer.write(chunk)
            if args.method == "execute":
                writer.write(b',"max-depth":' + str(args.max_depth).encode())
            writer.write(b'}}\n')


if __name__ == "__main__":
    main()
