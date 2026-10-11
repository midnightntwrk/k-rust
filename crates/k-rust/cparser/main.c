#include "node.h"
#include "krust_literals.h"
#include "parser.tab.h"
#include "scanner.h"

#include <assert.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct string_buffer {
  FILE *fp;
  char *buf;
  size_t capacity;
  size_t idx;
};

struct string_buffer string_buffer_new_memory(size_t initial) {
  assert(initial > 0 && "Invalid initial capacity");

  char *buf = malloc(sizeof(*buf) * initial);
  buf[0] = '\0';

  struct string_buffer ret
      = {.fp = NULL, .buf = buf, .capacity = initial, .idx = 0};
  return ret;
}

struct string_buffer string_buffer_new_file(FILE *fp) {
  struct string_buffer ret = {.fp = fp, .buf = NULL, .capacity = 0, .idx = 0};
  return ret;
}

void string_buffer_grow(struct string_buffer *sb) {
  if (sb->fp) {
    return;
  }

  size_t old_cap = sb->capacity;
  size_t new_cap = old_cap * 2;

  sb->buf = realloc(sb->buf, new_cap);
  sb->buf[old_cap] = 0;
  sb->capacity = new_cap;
}

int buf_printf(struct string_buffer *sb, char const *format, ...) {
  va_list args;
  va_start(args, format);

  if (sb->fp) {
    va_list copy;
    va_copy(copy, args);
    int result = vfprintf(sb->fp, format, copy);
    va_end(copy);

    va_end(args);
    return result;
  } else {
    va_list copy;
    va_copy(copy, args);
    int required = vsnprintf(NULL, 0, format, copy) + 1;
    va_end(copy);

    while ((sb->capacity - sb->idx) < required) {
      string_buffer_grow(sb);
    }

    va_list copy_2;
    va_copy(copy_2, args);
    vsnprintf(sb->buf + sb->idx, required, format, args);
    va_end(copy_2);

    sb->idx += required - 1;
    va_end(args);
    return required;
  }
}

/* A KORE string literal being written. */
struct krust_literal {
  char *text;
  size_t length;
  size_t capacity;
};

static void krust_literal_append(
    struct krust_literal *literal, const char *text, size_t length) {
  if (literal->length + length + 1 > literal->capacity) {
    size_t capacity = literal->capacity ? literal->capacity : 16;
    while (capacity < literal->length + length + 1)
      capacity *= 2;
    char *grown = realloc(literal->text, capacity);
    if (!grown) {
      perror("krust_kore_literal");
      exit(1);
    }
    literal->text = grown;
    literal->capacity = capacity;
  }
  memcpy(literal->text + literal->length, text, length);
  literal->length += length;
  literal->text[literal->length] = '\0';
}

/* Writes `code_point` as a KORE literal writes it: by the escape that names it, as itself if it
   is unescaped, and otherwise by the first hexadecimal escape whose digits hold it. */
static void krust_literal_code_point(struct krust_literal *literal, uint32_t code_point) {
  for (size_t index = 0; index < KRUST_ESCAPES(krust_kore_named_escapes); ++index) {
    if (krust_kore_named_escapes[index].code_point == code_point) {
      char escape[2] = {'\\', krust_kore_named_escapes[index].letter};
      krust_literal_append(literal, escape, 2);
      return;
    }
  }
  if (code_point >= KRUST_KORE_UNESCAPED_FIRST && code_point <= KRUST_KORE_UNESCAPED_LAST) {
    char character = (char)code_point;
    krust_literal_append(literal, &character, 1);
    return;
  }
  for (size_t index = 0; index < KRUST_ESCAPES(krust_kore_hex_escapes); ++index) {
    const struct krust_hex_escape *escape = &krust_kore_hex_escapes[index];
    if (((uint64_t)code_point >> (4 * escape->digits)) == 0) {
      char text[16];
      int length = snprintf(
          text, sizeof text, "\\%c%0*" PRIx32, escape->letter, escape->digits, code_point);
      krust_literal_append(literal, text, (size_t)length);
      return;
    }
  }
  abort(); /* the longest escape holds every code point */
}

/* The code point of the UTF-8 sequence that begins `text`, which is NUL-terminated, and its length
   in `*length`; a byte that begins no sequence is the code point of its value, of length 1. */
static uint32_t krust_utf8_next(const unsigned char *text, size_t *length) {
  unsigned char lead = text[0];
  size_t count;
  uint32_t code_point;
  uint32_t least;
  *length = 1;
  if (lead >= 0xc2 && lead <= 0xdf) {
    count = 2, code_point = lead & 0x1f, least = 0x80;
  } else if (lead >= 0xe0 && lead <= 0xef) {
    count = 3, code_point = lead & 0x0f, least = 0x800;
  } else if (lead >= 0xf0 && lead <= 0xf4) {
    count = 4, code_point = lead & 0x07, least = 0x10000;
  } else {
    return lead;
  }
  for (size_t index = 1; index < count; ++index) {
    if ((text[index] & 0xc0) != 0x80)
      return lead;
    code_point = (code_point << 6) | (text[index] & 0x3f);
  }
  if (code_point < least || code_point > 0x10ffff ||
      (code_point >= 0xd800 && code_point <= 0xdfff))
    return lead;
  *length = count;
  return code_point;
}

/* Writes the bytes of the UTF-8 encoding of `code_point`, each as the code point of its value. */
static void krust_literal_utf8_bytes(struct krust_literal *literal, uint32_t code_point) {
  if (code_point < 0x80) {
    krust_literal_code_point(literal, code_point);
  } else if (code_point < 0x800) {
    krust_literal_code_point(literal, 0xc0 | (code_point >> 6));
    krust_literal_code_point(literal, 0x80 | (code_point & 0x3f));
  } else if (code_point < 0x10000) {
    krust_literal_code_point(literal, 0xe0 | (code_point >> 12));
    krust_literal_code_point(literal, 0x80 | ((code_point >> 6) & 0x3f));
    krust_literal_code_point(literal, 0x80 | (code_point & 0x3f));
  } else {
    krust_literal_code_point(literal, 0xf0 | (code_point >> 18));
    krust_literal_code_point(literal, 0x80 | ((code_point >> 12) & 0x3f));
    krust_literal_code_point(literal, 0x80 | ((code_point >> 6) & 0x3f));
    krust_literal_code_point(literal, 0x80 | (code_point & 0x3f));
  }
}

static bool krust_is_scalar(uint32_t code_point) {
  return code_point <= 0x10ffff && !(code_point >= 0xd800 && code_point <= 0xdfff);
}

/* The number of `digits` digits of `base` at `*text`, which it advances past them; false if one
   of them is not such a digit. */
static bool krust_read_number(
    const unsigned char **text, int digits, int base, uint32_t *number) {
  *number = 0;
  for (int index = 0; index < digits; ++index) {
    unsigned char digit = **text;
    uint32_t value;
    if (digit >= '0' && digit <= '9')
      value = digit - '0';
    else if (digit >= 'a' && digit <= 'f')
      value = digit - 'a' + 10;
    else if (digit >= 'A' && digit <= 'F')
      value = digit - 'A' + 10;
    else
      return false;
    if (value >= (uint32_t)base)
      return false;
    *number = *number * base + value;
    ++*text;
  }
  return true;
}

/* Writes the code points of the body of a K String or Bytes literal, from `text` up to the closing
   quote at `end`; returns NULL or the reason the body is not one. */
static const char *krust_literal_k_body(
    struct krust_literal *literal, const unsigned char *text, const unsigned char *end,
    bool bytes) {
  while (text < end) {
    if (*text != '\\') {
      size_t length;
      uint32_t code_point = krust_utf8_next(text, &length);
      if (bytes) {
        for (size_t index = 0; index < length; ++index)
          krust_literal_code_point(literal, text[index]);
      } else {
        krust_literal_code_point(literal, code_point);
      }
      text += length;
      continue;
    }
    ++text;
    if (text == end)
      return "truncated escape";
    unsigned char escape = *text++;
    const struct krust_named_escape *named = NULL;
    for (size_t index = 0; index < KRUST_ESCAPES(krust_k_named_escapes); ++index)
      if ((unsigned char)krust_k_named_escapes[index].letter == escape)
        named = &krust_k_named_escapes[index];
    if (named) {
      krust_literal_code_point(literal, (uint32_t)named->code_point);
      continue;
    }
    const struct krust_hex_escape *hex = NULL;
    for (size_t index = 0; index < KRUST_ESCAPES(krust_k_hex_escapes); ++index)
      if ((unsigned char)krust_k_hex_escapes[index].letter == escape)
        hex = &krust_k_hex_escapes[index];
    uint32_t number;
    if (hex) {
      if (end - text < hex->digits)
        return "truncated Unicode escape";
      if (!krust_read_number(&text, hex->digits, 16, &number))
        return "invalid Unicode escape";
      if (bytes && hex->digits <= KRUST_K_BYTE_DIGITS) {
        krust_literal_code_point(literal, number);
      } else if (!krust_is_scalar(number)) {
        return "invalid Unicode scalar";
      } else if (bytes) {
        krust_literal_utf8_bytes(literal, number);
      } else {
        krust_literal_code_point(literal, number);
      }
    } else if (escape >= '0' && escape <= '9') {
      --text;
      if (end - text < KRUST_K_OCTAL_DIGITS)
        return "truncated octal escape";
      if (!krust_read_number(&text, KRUST_K_OCTAL_DIGITS, 8, &number))
        return "invalid octal escape";
      if (bytes && number > 0xff)
        return "octal byte escape out of range";
      krust_literal_code_point(literal, number);
    } else {
      return "unsupported escape";
    }
  }
  return NULL;
}

char *krust_kore_literal(
    const char *token, enum krust_token_kind kind, const char *sort, char **error) {
  struct krust_literal literal = {NULL, 0, 0};
  krust_literal_append(&literal, "\"", 1);
  const unsigned char *text = (const unsigned char *)token;
  const char *reason = NULL;
  switch (kind) {
  case KRUST_TOKEN_TEXT:
    while (*text) {
      size_t length;
      krust_literal_code_point(&literal, krust_utf8_next(text, &length));
      text += length;
    }
    break;
  case KRUST_TOKEN_BYTES:
    if (*text != 'b') {
      reason = "expected a leading `b`";
      break;
    }
    ++text;
    /* fall through */
  case KRUST_TOKEN_STRING: {
    size_t length = strlen((const char *)text);
    if (length < 2 || text[0] != '"' || text[length - 1] != '"')
      reason = "expected a double-quoted string";
    else
      reason = krust_literal_k_body(
          &literal, text + 1, text + length - 1, kind == KRUST_TOKEN_BYTES);
    break;
  }
  }
  if (reason) {
    free(literal.text);
    const char *format = "invalid %s token: %s";
    int length = snprintf(NULL, 0, format, sort, reason) + 1;
    *error = malloc(length);
    snprintf(*error, length, format, sort, reason);
    return NULL;
  }
  krust_literal_append(&literal, "\"", 1);
  return literal.text;
}

static bool equalsSymbol(node *x0, node *x1) {
  return strcmp(x0->symbol, x1->symbol) == 0;
}

bool equalsNode(node *x0, node *x1) {
  if (x0->str != x1->str) {
    return false;
  }
  if (x0->str) {
    return strcmp(x0->symbol, x1->symbol) == 0;
  } else {
    if (!(equalsSymbol(x0, x1) && x0->nchildren == x1->nchildren)) {
      return false;
    }
    for (size_t i = 0; i < x0->nchildren; i++) {
      if (!equalsNode(x0->children[i], x1->children[i])) {
        return false;
      }
    }
    return true;
  }
}

// Define an ordering on nodes as follows:
//   - Any string node is < any constructor node
//   - String nodes are compared via strcmp
//   - Constructor nodes are:
//     - First compared by symbol via strcmp
//     - If their symbols are identical, they are compared recursively:
//       - First by their number of children
//       - Then lexicographically over their children
//
// Returns true if x0 < x1
bool ltNode(node *x0, node *x1) {
    if (x0->str && x1->str) {
        return strcmp(x0->symbol, x1->symbol) < 1;
    }

    if (x0->str && !x1->str) {
        return true;
    }

    if (!x0->str && x1->str) {
        return false;
    }

    if (!equalsSymbol(x0, x1)) {
        return strcmp(x0->symbol, x1->symbol) < 1;
    }

    if (x0->nchildren != x1->nchildren) {
        return x0->nchildren < x1->nchildren;
    }

    for (size_t i = 0; i < x0->nchildren; i++) {
        if (!equalsNode(x0->children[i], x1->children[i])) {
            return ltNode(x0->children[i], x1->children[i]);
        }
    }

    return false;
}

char *injSymbol(char *lesser, char *greater) {
  char *prefix = "inj{";
  char *infix = ", ";
  char *suffix = "}";
  size_t len = strlen(prefix) + strlen(suffix) + strlen(lesser)
               + strlen(greater) + strlen(infix) + 1;
  char *symbol = malloc(len);
  strcpy(symbol, prefix);
  strcat(symbol, lesser);
  strcat(symbol, infix);
  strcat(symbol, greater);
  strcat(symbol, suffix);
  return symbol;
}

YYSTYPE mergeAmb(YYSTYPE x0, YYSTYPE x1) {
  if (equalsNode(x0.nterm, x1.nterm)) {
    return x0;
  }

  if(ltNode(x1.nterm, x0.nterm)) {
    YYSTYPE tmp = x0;
    x0 = x1;
    x1 = tmp;
  }

  node *n = malloc(sizeof(node) + sizeof(node *) * 2);
  node *x0n = x0.nterm;
  node *x1n = x1.nterm;
  char *prefix = "Lblamb{";
  char *suffix = "}";
  size_t len = strlen(prefix) + strlen(suffix) + strlen(x0n->sort) + 1;
  char *symbol = malloc(len);
  strcpy(symbol, prefix);
  strcat(symbol, x0n->sort);
  strcat(symbol, suffix);
  n->location = x0n->location;
  n->hasLocation = false;
  n->symbol = symbol;
  n->sort = x0n->sort;
  n->str = false;
  n->nchildren = 2;
  n->children[0] = x0n;
  n->children[1] = x1n;
  YYSTYPE result = {.nterm = n};
  return result;
}

void print(struct string_buffer *sb, node *current) {
  if (current->hasLocation) {
    buf_printf(sb, "Lbl'Hash'location{");
    buf_printf(sb, "%s", current->sort);
    buf_printf(sb, "}(");
  }
  buf_printf(sb, "%s", current->symbol);
  if (!current->str) {
    buf_printf(sb, "(");
    for (int i = 0; i < current->nchildren; i++) {
      node *child = current->children[i];
      print(sb, child);
      if (i != current->nchildren - 1)
        buf_printf(sb, ",");
    }
    buf_printf(sb, ")");
  }
  if (current->hasLocation) {
    buf_printf(
        sb,
        ", \\dv{SortString{}}(%s), \\dv{SortInt{}}(\"%d\"), "
        "\\dv{SortInt{}}(\"%d\"), \\dv{SortInt{}}(\"%d\"), "
        "\\dv{SortInt{}}(\"%d\"))",
        krust_kore_literal(current->location.filename, KRUST_TOKEN_TEXT, "String", NULL),
        current->location.first_line,
        current->location.first_column, current->location.last_line,
        current->location.last_column);
  }
}

/* Every byte the scanner has read in this parse, in order: a token subsort reads the text of its
   phrase from here, by the phrase's byte span, after the scanner may have read past it. */
static char *krust_input = NULL;
static size_t krust_input_length = 0, krust_input_capacity = 0;

void krust_read(YYLTYPE *location, const char *text, size_t length) {
  if (krust_input_capacity - krust_input_length < length) {
    size_t capacity = krust_input_capacity ? krust_input_capacity : 4096;
    while (capacity - krust_input_length < length) {
      if (capacity > SIZE_MAX / 2) {
        fprintf(stderr, "the input does not fit in memory\n");
        exit(1);
      }
      capacity *= 2;
    }
    char *input = realloc(krust_input, capacity);
    if (!input) {
      fprintf(stderr, "the input does not fit in memory\n");
      exit(1);
    }
    krust_input = input;
    krust_input_capacity = capacity;
  }
  memcpy(krust_input + krust_input_length, text, length);
  location->first_offset = krust_input_length;
  krust_input_length += length;
  location->last_offset = krust_input_length;
}

char *krust_read_text(const YYLTYPE *location) {
  assert(location->first_offset <= location->last_offset);
  assert(location->last_offset <= krust_input_length);
  size_t length = location->last_offset - location->first_offset;
  char *text = malloc(length + 1);
  memcpy(text, krust_input + location->first_offset, length);
  text[length] = '\0';
  return text;
}

extern node *result;
extern char *filename;

static void parse_internal(
    struct string_buffer *sb, char *program_name, char *input_file,
    char *location_file) {
  yyscan_t scanner;
  yylex_init(&scanner);

  filename = location_file;
  krust_input_length = 0;

  FILE *f = fopen(input_file, "r");
  if (!f) {
    int len = strlen(program_name) + strlen(input_file) + 19;
    char *buf = malloc(len);
    snprintf(buf, len, "%s: cannot access '%s'", program_name, input_file);
    perror(buf);
    exit(1);
  }

  yyset_in(f, scanner);

  int status = yyparse(scanner);
  if (status) {
    exit(status);
  }

  print(sb, result);
  yylex_destroy(scanner);
}

#define CONCAT(X, Y) X##Y
#define NAME(sort) CONCAT(parse_, sort)
#define PARSER_FUNCTION NAME(K_BISON_PARSER_SORT)

#define XSTR(S) #S
#define STR(S) XSTR(S)

char *PARSER_FUNCTION(char *input_file, char *location_file) {
  struct string_buffer sb = string_buffer_new_memory(1024);

  if (!location_file) {
    location_file = input_file;
  }

  parse_internal(&sb, STR(PARSER_FUNCTION), input_file, location_file);
  return sb.buf;
}

#ifdef K_BISON_PARSER_MAIN

int main(int argc, char **argv) {
  if (argc < 2 || argc > 3) {
    fprintf(stderr, "usage: %s <file> [<filename>]\n", argv[0]);
    exit(1);
  }

  char *location_file;
  if (argc == 3) {
    location_file = argv[2];
  } else {
    location_file = argv[1];
  }

  struct string_buffer sb = string_buffer_new_file(stdout);
  parse_internal(&sb, argv[0], argv[1], location_file);
  printf("\n");
}

#endif
