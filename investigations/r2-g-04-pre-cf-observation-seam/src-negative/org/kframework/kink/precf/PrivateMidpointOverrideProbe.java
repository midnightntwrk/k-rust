package org.kframework.kink.precf;

import java.io.File;
import java.util.List;
import org.kframework.definition.Definition;
import org.kframework.kompile.DefinitionParsing;
import org.kframework.kompile.KompileOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.ParserUtils;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.options.InnerParsingOptions;
import org.kframework.utils.options.OuterParsingOptions;

/** Must fail to compile: the one-argument typed parse/generate operation is private. */
public final class PrivateMidpointOverrideProbe extends DefinitionParsing {
  public PrivateMidpointOverrideProbe(
      List<File> lookupDirectories,
      KompileOptions options,
      OuterParsingOptions outerParsingOptions,
      InnerParsingOptions innerParsingOptions,
      GlobalOptions globalOptions,
      KExceptionManager kem,
      FileUtil files,
      ParserUtils parser,
      boolean cacheParses,
      File cacheFile,
      Stopwatch stopwatch) {
    super(
        lookupDirectories,
        options,
        outerParsingOptions,
        innerParsingOptions,
        globalOptions,
        kem,
        files,
        parser,
        cacheParses,
        cacheFile,
        stopwatch);
  }

  @Override
  protected Definition resolveConfigBubbles(Definition definition) {
    return definition;
  }
}
