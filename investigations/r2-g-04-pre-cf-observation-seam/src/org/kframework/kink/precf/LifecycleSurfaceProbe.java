package org.kframework.kink.precf;

import java.io.File;
import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.List;
import org.kframework.compile.GenerateSentencesFromConfigDecl;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kompile.DefinitionParsing;
import org.kframework.kompile.Kompile;
import org.kframework.kompile.KompileOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.ParserUtils;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.options.InnerParsingOptions;
import org.kframework.utils.options.OuterParsingOptions;

/** Installed-artifact signature probe for the strongest non-forbidden pre-CF candidate. */
public class LifecycleSurfaceProbe extends DefinitionParsing {
  public LifecycleSurfaceProbe(
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

  /** This override is admissible, but its input still contains bubbles and super returns post-CF. */
  @Override
  protected Definition resolveConfigBubbles(
      Definition definition, Module defaultConfiguration) {
    return super.resolveConfigBubbles(definition, defaultConfiguration);
  }

  public static void main(String[] args) throws Exception {
    if (args.length != 1 || !(args[0].equals("identity") || args[0].equals("augmentation"))) {
      throw new IllegalArgumentException("expected identity or augmentation mode");
    }
    String mode = args[0];
    Method entry =
        DefinitionParsing.class.getDeclaredMethod(
            "parseDefinitionAndResolveBubbles",
            File.class,
            KompileOptions.MainModule.class,
            KompileOptions.SyntaxModule.class,
            java.util.Set.class);
    Method wrapper =
        DefinitionParsing.class.getDeclaredMethod(
            "resolveConfigBubbles", Definition.class, Module.class);
    Method midpoint =
        DefinitionParsing.class.getDeclaredMethod("resolveConfigBubbles", Definition.class);
    Method generator =
        GenerateSentencesFromConfigDecl.class.getDeclaredMethod(
            "gen",
            KExceptionManager.class,
            org.kframework.kore.K.class,
            org.kframework.kore.K.class,
            org.kframework.attributes.Att.class,
            Module.class);
    Field parserField = Kompile.class.getDeclaredField("definitionParsing");

    require(Modifier.isPublic(entry.getModifiers()), "entry is not public");
    require(Modifier.isProtected(wrapper.getModifiers()), "wrapper is not protected");
    require(Modifier.isPrivate(midpoint.getModifiers()), "typed midpoint operation is not private");
    require(Modifier.isPublic(generator.getModifiers()), "generator is not public");
    require(Modifier.isStatic(generator.getModifiers()), "generator is not static");
    require(Modifier.isPrivate(parserField.getModifiers()), "Kompile parser field is not private");
    require(Modifier.isFinal(parserField.getModifiers()), "Kompile parser field is not final");

    String verdict =
        mode.equals("identity")
            ? "protected-wrapper-delegation-compiles"
            : "blocked-private-typed-midpoint";
    System.out.println("{");
    field("mode", mode, false);
    field("verdict", verdict, false);
    field("entryVisibility", Modifier.toString(entry.getModifiers()), false);
    field("wrapperVisibility", Modifier.toString(wrapper.getModifiers()), false);
    field("midpointVisibility", Modifier.toString(midpoint.getModifiers()), false);
    field("generatorVisibility", Modifier.toString(generator.getModifiers()), false);
    field("kompileParserFieldVisibility", Modifier.toString(parserField.getModifiers()), false);
    field("wrapperInput", "Definition-with-configuration-Bubbles", false);
    field("wrapperOutput", "Definition-after-CF-generation", false);
    field("typedConfigurationInterceptable", "false", true);
    System.out.println("}");
  }

  private static void require(boolean condition, String message) {
    if (!condition) {
      throw new AssertionError(message);
    }
  }

  private static void field(String name, String value, boolean last) {
    System.out.println(
        "  \"" + name + "\": \"" + value + "\"" + (last ? "" : ","));
  }
}
