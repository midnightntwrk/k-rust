# R2-G-04 commands

All material commands run from the R2-G-04 worktree. The executable source of
truth is `verify.sh`; it contains every pin check, source/jar hash check,
`javap`, `javac`, Java probe, prior replay, compiler, runtime, projection, and
comparison command with exact arguments and redirections.

The accepted command is:

```sh
bun run r2:g:pre-cf-seam
```

The first complete probe cycle was also run explicitly as:

```sh
bash investigations/r2-g-04-pre-cf-observation-seam/verify.sh \
  investigations/r2-g-04-pre-cf-observation-seam/build/verify-2
```

The initial bounded compile/signature development probes were:

```sh
javap -classpath "$K_JAVA/*" -p org.kframework.kompile.DefinitionParsing
javap -classpath "$K_JAVA/*" -p org.kframework.kompile.Kompile
javap -classpath "$K_JAVA/*" -p \
  org.kframework.compile.GenerateSentencesFromConfigDecl
javac -encoding UTF-8 -cp "$K_JAVA/*" \
  investigations/r2-g-04-pre-cf-observation-seam/src/.../LifecycleSurfaceProbe.java
javac -encoding UTF-8 -cp "$K_JAVA/*" \
  investigations/r2-g-04-pre-cf-observation-seam/src-negative/.../PrivateMidpointOverrideProbe.java
```

Read-only lifecycle audit commands used `git rev-parse`, `git status`, `rg`,
`sed`, `nl`, `javap`, `sha256sum`, `command -v`, `readlink -f`, `java -version`,
`javac -version`, and `uname` against the exact sources and installed artifacts
listed in `results.json`. No official source or installed artifact was changed.

Final repository checks are:

```sh
bun run check
git diff --check
```
