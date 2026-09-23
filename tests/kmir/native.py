#!/usr/bin/env python3
"""Persistent K-Rust execution support for the KMIR qualification corpus."""

from __future__ import annotations

import argparse
import ast
import json
from pathlib import Path
import re
import sys
from typing import Any, Mapping

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from support import GateError  # noqa: E402
from support.hashing import canonical_json, json_sha256  # noqa: E402
from support.pins import load_toml  # noqa: E402
from support.process import run  # noqa: E402


def application(name: str, *arguments: str) -> str:
    return f"Lbl{name}{{}}({','.join(arguments)})"


def integer(value: str | int) -> str:
    return f'\\dv{{SortInt{{}}}}("{int(value)}")'


def boolean(value: str) -> str:
    if value not in {"true", "false"}:
        raise GateError(f"invalid concrete Bool: {value}")
    return f'\\dv{{SortBool{{}}}}("{value}")'


TOKEN = re.compile(
    r'\s*(b"(?:\\x[0-9a-fA-F]{2})*"|"(?:\\.|[^"\\])*"|\|->|\.[A-Za-z]+|-?[0-9]+|[A-Za-z][A-Za-z0-9]*|[(),;:])'
)


class Parser:
    def __init__(self, source: str) -> None:
        self.tokens = []
        offset = 0
        for match in TOKEN.finditer(source):
            if source[offset : match.start()].strip():
                raise GateError(f"cannot tokenize KMIR term near: {source[offset:]}")
            self.tokens.append(match.group(1))
            offset = match.end()
        if source[offset:].strip():
            raise GateError(f"cannot tokenize KMIR term near: {source[offset:]}")
        self.index = 0

    def peek(self) -> str | None:
        return self.tokens[self.index] if self.index < len(self.tokens) else None

    def take(self, expected: str | None = None) -> str:
        token = self.peek()
        if token is None or expected is not None and token != expected:
            raise GateError(f"expected {expected!r}, found {token!r} in {self.tokens}")
        self.index += 1
        return token

    def term(self) -> Any:
        name = self.take()
        if name.lstrip("-").isdigit() or name in {"true", "false"} or name.startswith("."):
            return name
        if self.peek() != "(":
            return name
        self.take("(")
        arguments = []
        if self.peek() != ")":
            while True:
                arguments.append(self.sequence())
                if self.peek() != ",":
                    break
                self.take(",")
        self.take(")")
        return name, arguments

    def tyss_tail(self, items: list[Any]) -> Any:
        while self.peek() == ":":
            self.take(":")
            if self.peek() == ".Tyss":
                self.take(".Tyss")
                return "Tyss", items
            first = self.term()
            if first == ".Tys":
                items.append(("Tys", []))
                continue
            if not isinstance(first, tuple) or first[0] != "ty":
                raise GateError(f"unsupported Tys head: {first}")
            fields = [first]
            while self.peek() == "ty":
                fields.append(self.term())
            self.take(".Tys")
            items.append(("Tys", fields))
        raise GateError("Tyss sequence has no .Tyss terminator")

    def sequence(self) -> Any:
        first = self.term()
        if self.peek() == "|->":
            items = []
            key = first
            while True:
                self.take("|->")
                items.append((key, self.term()))
                if self.peek() != ",":
                    break
                self.take(",")
                key = self.term()
            self.take(".Map")
            return "Map", items
        if isinstance(first, tuple) and first[0] == "ListItem":
            items = [first[1][0]]
            while self.peek() == "ListItem":
                item = self.term()
                items.append(item[1][0])
            self.take(".List")
            return "List", items
        if first == ".Tys" and self.peek() == ":":
            return self.tyss_tail([first])
        if isinstance(first, tuple) and first[0] == "discriminant":
            items = [first]
            while self.peek() == "discriminant":
                items.append(self.term())
            self.take(".Discriminants")
            return "Discriminants", items
        projection_names = {
            "projectionElemConstantIndex",
            "projectionElemDeref",
            "projectionElemDowncast",
            "projectionElemField",
            "projectionElemIndex",
            "projectionElemSingletonArray",
            "projectionElemWrapStruct",
            "projectionElemToZST",
            "projectionElemFromZST",
            "projectionElemSubslice",
            "PointerOffset",
        }
        first_name = first[0] if isinstance(first, tuple) else first
        if first_name in projection_names:
            items = [first]
            while self.peek() in projection_names:
                items.append(self.term())
            self.take(".ProjectionElems")
            return "Projections", items
        if first_name == "ty":
            items = [first]
            while self.peek() == "ty":
                items.append(self.term())
            if self.peek() == ".Tys":
                self.take(".Tys")
                parsed = "Tys", items
                if self.peek() == ":":
                    return self.tyss_tail([parsed])
                return parsed
        if first_name == "machineSize":
            items = [first]
            while self.peek() == "machineSize":
                items.append(self.term())
            if self.peek() == ".MachineSizes":
                self.take(".MachineSizes")
                return "MachineSizes", items
        if first_name == "layoutShape":
            items = [first]
            while self.peek() == "layoutShape":
                items.append(self.term())
            if self.peek() == ".LayoutShapes":
                self.take(".LayoutShapes")
                return "LayoutShapes", items
        if isinstance(first, tuple) and first[0] == "provenanceMapEntry":
            items = [first]
            while self.peek() == "provenanceMapEntry":
                items.append(self.term())
            self.take(".ProvenanceMapEntries")
            return "ProvenanceMapEntries", items
        if isinstance(first, tuple) and first[0] == "branch":
            items = [first]
            while self.peek() == "branch":
                items.append(self.term())
            self.take(".Branches")
            return "Branches", items
        if first_name in {"const", "operandConstant", "copy", "move"}:
            items = [first]
            while self.peek() in {"const", "operandConstant", "copy", "move"}:
                items.append(self.term())
            if self.peek() == ".Operands":
                self.take(".Operands")
                return "Operands", items
        if first_name in {
            "genericArgKindLifetime",
            "genericArgKindType",
            "genericArgKindConst",
        }:
            items = [first]
            while self.peek() in {
                "genericArgKindLifetime",
                "genericArgKindType",
                "genericArgKindConst",
            }:
                items.append(self.term())
            self.take(".GenericArgs")
            return "GenericArgs", items
        if first_name == "localDecl":
            items = [first]
            while self.peek() == "localDecl":
                items.append(self.term())
            self.take(".LocalDecls")
            return "LocalDecls", items
        items = [first]
        while self.peek() == ";":
            self.take(";")
            items.append(self.term())
        return items[0] if len(items) == 1 else (";", items)


def parse_term(source: str) -> Any:
    parser = Parser(source)
    term = parser.sequence()
    if parser.peek() is not None:
        raise GateError(f"unparsed KMIR term suffix: {parser.tokens[parser.index:]}")
    return term


def int_argument(term: Any) -> str:
    if isinstance(term, str) and term.lstrip("-").isdigit():
        return integer(term)
    if isinstance(term, tuple) and term[0] == "local" and len(term[1]) == 1:
        return int_argument(term[1][0])
    raise GateError(f"expected concrete local/Int: {term}")


def bytes_argument(term: Any) -> str:
    if not isinstance(term, str):
        raise GateError(f"expected concrete Bytes: {term}")
    value = ast.literal_eval(term)
    if not isinstance(value, bytes):
        raise GateError(f"expected concrete Bytes: {term}")
    encoded = '"' + "".join(f"\\x{byte:02x}" for byte in value) + '"'
    return f"\\dv{{SortBytes{{}}}}({encoded})"


def string_argument(term: Any) -> str:
    if not isinstance(term, str):
        raise GateError(f"expected concrete String: {term}")
    value = ast.literal_eval(term)
    if not isinstance(value, str):
        raise GateError(f"expected concrete String: {term}")
    return f"\\dv{{SortString{{}}}}({json.dumps(value)})"


def mir_value(term: Any) -> str:
    if term == "Moved":
        return application("moved")
    if not isinstance(term, tuple):
        raise GateError(f"unsupported MirValue: {term}")
    if term[0] == "Integer" and len(term[1]) == 3 and term[1][2] in {"true", "false"}:
        return application(
            "integer",
            int_argument(term[1][0]),
            int_argument(term[1][1]),
            boolean(term[1][2]),
        )
    if term[0] == "BoolVal" and len(term[1]) == 1 and term[1][0] in {"true", "false"}:
        return application("boolean", boolean(term[1][0]))
    if term[0] == "Aggregate" and len(term[1]) == 2:
        variant = term[1][0]
        if not isinstance(variant, tuple) or variant[0] != "variantIdx" or len(variant[1]) != 1:
            raise GateError(f"unsupported aggregate variant: {variant}")
        raw_fields = term[1][1]
        if raw_fields == ".List":
            fields = []
        elif isinstance(raw_fields, tuple) and raw_fields[0] == "List":
            fields = raw_fields[1]
        else:
            raise GateError(f"unsupported aggregate fields: {raw_fields}")
        result = application("'Stop'List")
        for field in reversed(fields):
            item = application(
                "ListItem",
                f"inj{{SortMirValue{{}},SortKItem{{}}}}({mir_value(field)})",
            )
            result = application("'Unds'List'Unds'", item, result)
        return application("aggregate", int_argument(variant[1][0]), result)
    if term[0] == "Union" and len(term[1]) == 2:
        field = term[1][0]
        if not isinstance(field, tuple) or field[0] != "fieldIdx" or len(field[1]) != 1:
            raise GateError(f"unsupported union field: {field}")
        return application(
            "union",
            int_argument(field[1][0]),
            mir_value(term[1][1]),
        )
    if term[0] == "Range" and len(term[1]) == 1:
        raw_elements = term[1][0]
        if raw_elements == ".List":
            elements = []
        elif isinstance(raw_elements, tuple) and raw_elements[0] == "List":
            elements = raw_elements[1]
        else:
            raise GateError(f"unsupported range elements: {raw_elements}")
        result = application("'Stop'List")
        for element in reversed(elements):
            item = application(
                "ListItem",
                f"inj{{SortMirValue{{}},SortKItem{{}}}}({mir_value(element)})",
            )
            result = application("'Unds'List'Unds'", item, result)
        return application("range", result)
    if term[0] == "Reference" and len(term[1]) == 4:
        return application(
            "reference",
            int_argument(term[1][0]),
            place(term[1][1]),
            mutability(term[1][2]),
            metadata(term[1][3]),
        )
    if term[0] == "PtrLocal" and len(term[1]) == 4:
        return application(
            "pointer",
            int_argument(term[1][0]),
            place(term[1][1]),
            mutability(term[1][2]),
            metadata(term[1][3]),
        )
    if term[0] == "AllocRef" and len(term[1]) == 3:
        return application(
            "allocationReference",
            alloc_id(term[1][0]),
            projections(term[1][1]),
            metadata(term[1][2]),
        )
    raise GateError(f"unsupported MirValue: {term}")


def alloc_id(term: Any) -> str:
    if isinstance(term, tuple) and term[0] == "allocId" and len(term[1]) == 1:
        return application("allocId", int_argument(term[1][0]))
    raise GateError(f"unsupported AllocId: {term}")


def ty(term: Any) -> str:
    if isinstance(term, tuple) and term[0] == "ty" and len(term[1]) == 1:
        return application("tyId", int_argument(term[1][0]))
    raise GateError(f"unsupported Ty: {term}")


def type_info(term: Any) -> str:
    if isinstance(term, tuple) and term[0] == "typeInfoPrimitiveType" and len(term[1]) == 1:
        return application("primitiveType", primitive_type(term[1][0]))
    if isinstance(term, tuple) and term[0] == "typeInfoArrayType" and len(term[1]) == 2:
        return application("arrayType", ty(term[1][0]), maybe_ty_const(term[1][1]))
    if isinstance(term, tuple) and term[0] == "typeInfoPtrType" and len(term[1]) == 1:
        return application("pointerType", ty(term[1][0]))
    if isinstance(term, tuple) and term[0] == "typeInfoRefType" and len(term[1]) == 1:
        return application("referenceType", ty(term[1][0]))
    if isinstance(term, tuple) and term[0] == "typeInfoStructType" and len(term[1]) == 4:
        return application(
            "structType",
            string_argument(term[1][0]),
            adt_def(term[1][1]),
            tys(term[1][2]),
            maybe_layout_shape(term[1][3]),
        )
    if isinstance(term, tuple) and term[0] == "typeInfoUnionType" and len(term[1]) == 4:
        return application(
            "unionType",
            string_argument(term[1][0]),
            adt_def(term[1][1]),
            tys(term[1][2]),
            maybe_layout_shape(term[1][3]),
        )
    if isinstance(term, tuple) and term[0] == "typeInfoTupleType" and len(term[1]) == 2:
        return application(
            "tupleType",
            tys(term[1][0]),
            maybe_layout_shape(term[1][1]),
        )
    if isinstance(term, tuple) and term[0] == "typeInfoEnumType" and len(term[1]) == 5:
        return application(
            "enumType",
            string_argument(term[1][0]),
            adt_def(term[1][1]),
            discriminants(term[1][2]),
            tyss(term[1][3]),
            maybe_layout_shape(term[1][4]),
        )
    if isinstance(term, tuple) and term[0] == "TypeInfoDynType" and len(term[1]) == 2:
        return application(
            "dynamicType",
            string_argument(term[1][0]),
            maybe_layout_shape(term[1][1]),
        )
    if isinstance(term, tuple) and term[0] == "typeInfoFunType" and len(term[1]) == 1:
        return application("funType", string_argument(term[1][0]))
    if term == "typeInfoVoidType":
        return application("voidType")
    raise GateError(f"unsupported TypeInfo: {term}")


def primitive_type(term: Any) -> str:
    if term == "primTypeBool":
        return application("bool")
    if term == "primTypeChar":
        return application("char")
    if term == "primTypeStr":
        return application("str")
    if isinstance(term, tuple) and term[0] == "primTypeInt" and len(term[1]) == 1:
        names = {
            "intTyIsize": "isize",
            "intTyI8": "i8",
            "intTyI16": "i16",
            "intTyI32": "i32",
            "intTyI64": "i64",
            "intTyI128": "i128",
        }
        if term[1][0] in names:
            return application("signedInteger", application(names[term[1][0]]))
    if isinstance(term, tuple) and term[0] == "primTypeUint" and len(term[1]) == 1:
        names = {
            "uintTyUsize": "usize",
            "uintTyU8": "u8",
            "uintTyU16": "u16",
            "uintTyU32": "u32",
            "uintTyU64": "u64",
            "uintTyU128": "u128",
        }
        if term[1][0] in names:
            return application("unsignedInteger", application(names[term[1][0]]))
    if isinstance(term, tuple) and term[0] == "primTypeFloat" and len(term[1]) == 1:
        names = {
            "floatTyF16": "f16",
            "floatTyF32": "f32",
            "floatTyF64": "f64",
            "floatTyF128": "f128",
        }
        if term[1][0] in names:
            return application("float", application(names[term[1][0]]))
    raise GateError(f"unsupported PrimitiveType: {term}")


def adt_def(term: Any) -> str:
    if isinstance(term, tuple) and term[0] == "adtDef" and len(term[1]) == 1:
        return application("adtDef", int_argument(term[1][0]))
    raise GateError(f"unsupported AdtDef: {term}")


def tys(term: Any) -> str:
    if term == ".Tys":
        items = []
    elif isinstance(term, tuple) and term[0] == "Tys":
        items = term[1]
    else:
        raise GateError(f"unsupported Tys: {term}")
    result = application("tysEmpty")
    for item in reversed(items):
        result = application("tysCons", ty(item), result)
    return result


def tyss(term: Any) -> str:
    if term == ".Tyss":
        items = []
    elif isinstance(term, tuple) and term[0] == "Tyss":
        items = term[1]
    else:
        raise GateError(f"unsupported Tyss: {term}")
    result = application("tyssEmpty")
    for item in reversed(items):
        result = application("tyssCons", tys(item), result)
    return result


def discriminants(term: Any) -> str:
    if term == ".Discriminants":
        items = []
    elif isinstance(term, tuple) and term[0] == "Discriminants":
        items = term[1]
    else:
        raise GateError(f"unsupported Discriminants: {term}")
    result = application("discriminantsEmpty")
    for item in reversed(items):
        if not isinstance(item, tuple) or item[0] != "discriminant" or len(item[1]) != 1:
            raise GateError(f"unsupported Discriminant: {item}")
        result = application(
            "discriminantsCons",
            application("discriminant", int_argument(item[1][0])),
            result,
        )
    return result


def machine_size(term: Any) -> str:
    if isinstance(term, tuple) and term[0] == "machineSize" and len(term[1]) == 1:
        return application("machineSize", int_argument(term[1][0]))
    raise GateError(f"unsupported MachineSize: {term}")


def machine_sizes(term: Any) -> str:
    if term == ".MachineSizes":
        items = []
    elif isinstance(term, tuple) and term[0] == "MachineSizes":
        items = term[1]
    else:
        raise GateError(f"unsupported MachineSizes: {term}")
    result = application("machineSizesEmpty")
    for item in reversed(items):
        result = application("machineSizesCons", machine_size(item), result)
    return result


def maybe_layout_shape(term: Any) -> str:
    if term == "noLayoutShape":
        return application("noLayoutShape")
    if isinstance(term, tuple) and term[0] == "someLayoutShape" and len(term[1]) == 1:
        return application("someLayoutShape", layout_shape(term[1][0]))
    raise GateError(f"unsupported MaybeLayoutShape: {term}")


def layout_shape(term: Any) -> str:
    if not isinstance(term, tuple) or term[0] != "layoutShape" or len(term[1]) != 5:
        raise GateError(f"unsupported LayoutShape: {term}")
    fields = term[1][0]
    if not isinstance(fields, tuple) or fields[0] != "fieldsShapeArbitrary" or len(fields[1]) != 1:
        raise GateError(f"unsupported FieldsShape: {fields}")
    arbitrary = fields[1][0]
    if not isinstance(arbitrary, tuple) or arbitrary[0] != "mk" or len(arbitrary[1]) != 1:
        raise GateError(f"unsupported FieldsShapeArbitrary: {arbitrary}")
    alignment = term[1][3]
    if not isinstance(alignment, tuple) or alignment[0] != "align" or len(alignment[1]) != 1:
        raise GateError(f"unsupported layout Align: {alignment}")
    return application(
        "layoutShape",
        application(
            "fieldsShapeArbitrary",
            application("arbitraryFields", machine_sizes(arbitrary[1][0])),
        ),
        variants_shape(term[1][1]),
        value_abi(term[1][2]),
        application("align", int_argument(alignment[1][0])),
        machine_size(term[1][4]),
    )


def layout_shapes(term: Any) -> str:
    if term == ".LayoutShapes":
        items = []
    elif isinstance(term, tuple) and term[0] == "LayoutShapes":
        items = term[1]
    else:
        raise GateError(f"unsupported LayoutShapes: {term}")
    result = application("layoutShapesEmpty")
    for item in reversed(items):
        result = application("layoutShapesCons", layout_shape(item), result)
    return result


def variants_shape(term: Any) -> str:
    if not isinstance(term, tuple) or len(term[1]) != 1:
        raise GateError(f"unsupported VariantsShape: {term}")
    if term[0] == "variantsShapeSingle":
        single = term[1][0]
        if not isinstance(single, tuple) or single[0] != "mk" or len(single[1]) != 1:
            raise GateError(f"unsupported VariantsShapeSingle: {single}")
        variant = single[1][0]
        if not isinstance(variant, tuple) or variant[0] != "variantIdx" or len(variant[1]) != 1:
            raise GateError(f"unsupported VariantIdx: {variant}")
        return application(
            "variantsShapeSingle",
            application("singleVariant", int_argument(variant[1][0])),
        )
    if term[0] == "variantsShapeMultiple":
        multiple = term[1][0]
        if not isinstance(multiple, tuple) or multiple[0] != "mk" or len(multiple[1]) != 4:
            raise GateError(f"unsupported VariantsShapeMultiple: {multiple}")
        if multiple[1][1] == "tagEncodingDirect":
            tag_encoding = application("direct")
        elif multiple[1][1] == ("tagEncodingNiche", []):
            tag_encoding = application("niche")
        else:
            raise GateError(f"unsupported TagEncoding: {multiple[1][1]}")
        return application(
            "variantsShapeMultiple",
            application(
                "multipleVariants",
                scalar(multiple[1][0]),
                tag_encoding,
                int_argument(multiple[1][2]),
                layout_shapes(multiple[1][3]),
            ),
        )
    raise GateError(f"unsupported VariantsShape: {term}")


def scalar(term: Any) -> str:
    if not isinstance(term, tuple) or term[0] != "scalarInitialized" or len(term[1]) != 1:
        raise GateError(f"unsupported Scalar: {term}")
    initialized = term[1][0]
    if not isinstance(initialized, tuple) or initialized[0] != "mk" or len(initialized[1]) != 2:
        raise GateError(f"unsupported ScalarInitialized: {initialized}")
    primitive = initialized[1][0]
    if not isinstance(primitive, tuple) or len(primitive[1]) != 1:
        raise GateError(f"unsupported Primitive: {primitive}")
    if primitive[0] == "primitiveInt":
        integer_primitive = primitive[1][0]
        if not isinstance(integer_primitive, tuple) or integer_primitive[0] != "mk" or len(integer_primitive[1]) != 2:
            raise GateError(f"unsupported PrimitiveInt: {integer_primitive}")
        lengths = {
            "integerLengthI8": "lengthI8",
            "integerLengthI16": "lengthI16",
            "integerLengthI32": "lengthI32",
            "integerLengthI64": "lengthI64",
            "integerLengthI128": "lengthI128",
        }
        if integer_primitive[1][0] not in lengths:
            raise GateError(f"unsupported IntegerLength: {integer_primitive[1][0]}")
        converted_primitive = application(
            "integerPrimitive",
            application(
                "primitiveInt",
                application(lengths[integer_primitive[1][0]]),
                boolean(integer_primitive[1][1]),
            ),
        )
    elif primitive[0] == "primitivePointer":
        address_space = primitive[1][0]
        if not isinstance(address_space, tuple) or address_space[0] != "addressSpace" or len(address_space[1]) != 1:
            raise GateError(f"unsupported AddressSpace: {address_space}")
        converted_primitive = application(
            "pointerPrimitive",
            application("addressSpace", int_argument(address_space[1][0])),
        )
    else:
        raise GateError(f"unsupported Primitive: {primitive}")
    wrapping_range = initialized[1][1]
    if not isinstance(wrapping_range, tuple) or wrapping_range[0] != "wrappingRange" or len(wrapping_range[1]) != 2:
        raise GateError(f"unsupported WrappingRange: {wrapping_range}")
    return application(
        "initializedScalar",
        application(
            "scalarInitializedFields",
            converted_primitive,
            application(
                "wrappingRange",
                int_argument(wrapping_range[1][0]),
                int_argument(wrapping_range[1][1]),
            ),
        ),
    )


def value_abi(term: Any) -> str:
    if not isinstance(term, tuple) or len(term[1]) != 1:
        raise GateError(f"unsupported ValueAbi: {term}")
    if term[0] == "valueAbiScalar":
        return application("valueAbiScalar", scalar(term[1][0]))
    if term[0] == "valueAbiAggregate":
        aggregate = term[1][0]
        if not isinstance(aggregate, tuple) or aggregate[0] != "mk" or len(aggregate[1]) != 1 or aggregate[1][0] not in {"true", "false"}:
            raise GateError(f"unsupported ValueAbiAggregate: {aggregate}")
        return application(
            "valueAbiAggregate",
            application("aggregateAbi", boolean(aggregate[1][0])),
        )
    raise GateError(f"unsupported ValueAbi: {term}")


def maybe_ty_const(term: Any) -> str:
    if term == "noTyConst":
        return application("noTyConst")
    if isinstance(term, tuple) and term[0] == "someTyConst" and len(term[1]) == 1:
        return application("someTyConst", ty_const(term[1][0]))
    raise GateError(f"unsupported MaybeTyConst: {term}")


def ty_const(term: Any) -> str:
    if not isinstance(term, tuple) or term[0] != "tyConst" or len(term[1]) != 2:
        raise GateError(f"unsupported TyConst: {term}")
    identifier = term[1][1]
    if not isinstance(identifier, tuple) or identifier[0] != "tyConstId" or len(identifier[1]) != 1:
        raise GateError(f"unsupported TyConstId: {identifier}")
    return application(
        "tyConst",
        ty_const_kind(term[1][0]),
        application("tyConstId", int_argument(identifier[1][0])),
    )


def ty_const_kind(term: Any) -> str:
    if not isinstance(term, tuple) or term[0] != "tyConstKindValue" or len(term[1]) != 2:
        raise GateError(f"unsupported TyConstKind: {term}")
    return application(
        "value",
        ty(term[1][0]),
        allocation(term[1][1]),
    )


def allocation(term: Any) -> str:
    if not isinstance(term, tuple) or term[0] != "allocation" or len(term[1]) != 4:
        raise GateError(f"unsupported Allocation: {term}")
    alignment = term[1][2]
    if not isinstance(alignment, tuple) or alignment[0] != "align" or len(alignment[1]) != 1:
        raise GateError(f"unsupported Align: {alignment}")
    return application(
        "allocation",
        bytes_argument(term[1][0]),
        provenance_map(term[1][1]),
        application("align", int_argument(alignment[1][0])),
        mutability(term[1][3]),
    )


def provenance_map(term: Any) -> str:
    if not isinstance(term, tuple) or term[0] != "provenanceMap" or len(term[1]) != 1:
        raise GateError(f"unsupported ProvenanceMap: {term}")
    entries = term[1][0]
    if entries == ".ProvenanceMapEntries":
        return application("emptyProvenanceMap")
    if not isinstance(entries, tuple) or entries[0] != "ProvenanceMapEntries" or len(entries[1]) != 1:
        raise GateError(f"unsupported ProvenanceMap entries: {entries}")
    entry = entries[1][0]
    if not isinstance(entry, tuple) or entry[0] != "provenanceMapEntry" or len(entry[1]) != 2:
        raise GateError(f"unsupported ProvenanceMap entry: {entry}")
    return application(
        "singletonProvenanceMap",
        int_argument(entry[1][0]),
        alloc_id(entry[1][1]),
    )


def mutability(term: Any) -> str:
    if term == "mutabilityNot":
        return application("notMutable")
    if term == "mutabilityMut":
        return application("mutable")
    raise GateError(f"unsupported Mutability: {term}")


def metadata_size(term: Any) -> str:
    if term == "noMetadataSize":
        return application("noMetadataSize")
    if isinstance(term, tuple) and term[0] in {"staticSize", "dynamicSize"} and len(term[1]) == 1:
        return application(term[0], int_argument(term[1][0]))
    raise GateError(f"unsupported MetadataSize: {term}")


def metadata(term: Any) -> str:
    if not isinstance(term, tuple) or term[0] != "metadata" or len(term[1]) != 3:
        raise GateError(f"unsupported Metadata: {term}")
    return application(
        "metadata",
        metadata_size(term[1][0]),
        int_argument(term[1][1]),
        metadata_size(term[1][2]),
    )


def region(term: Any) -> str:
    if isinstance(term, tuple) and term[0] == "region" and term[1] == ["regionKindReErased"]:
        return application("erased")
    raise GateError(f"unsupported Region: {term}")


def borrow_kind(term: Any) -> str:
    if term == "borrowKindShared":
        return application("sharedBorrow")
    if isinstance(term, tuple) and term[0] == "borrowKindMut" and term[1] == ["mutBorrowKindDefault"]:
        return application("mutableBorrow")
    raise GateError(f"unsupported BorrowKind: {term}")


def projections(term: Any) -> str:
    if term == ".ProjectionElems":
        return application("projectionsEmpty")
    if isinstance(term, tuple) and term[0] == "Projections" and term[1]:
        result = application("projectionsEmpty")
        for projection in reversed(term[1]):
            if projection == "projectionElemDeref":
                head = application("deref")
            elif projection == "projectionElemSingletonArray":
                head = application("singletonArray")
            elif projection == "projectionElemWrapStruct":
                head = application("wrapStruct")
            elif projection == "projectionElemToZST":
                head = application("toZst")
            elif projection == "projectionElemFromZST":
                head = application("fromZst")
            elif isinstance(projection, tuple) and projection[0] == "projectionElemField" and len(projection[1]) == 2:
                index = projection[1][0]
                if not isinstance(index, tuple) or index[0] != "fieldIdx" or len(index[1]) != 1:
                    raise GateError(f"unsupported FieldIdx: {index}")
                head = application(
                    "field", int_argument(index[1][0]), ty(projection[1][1])
                )
            elif projection[0] == "projectionElemIndex" and len(projection[1]) == 1:
                head = application("index", int_argument(projection[1][0]))
            elif (
                projection[0] == "projectionElemConstantIndex"
                and len(projection[1]) == 3
                and projection[1][2] in {"true", "false"}
            ):
                head = application(
                    "constantIndex",
                    int_argument(projection[1][0]),
                    int_argument(projection[1][1]),
                    boolean(projection[1][2]),
                )
            elif (
                projection[0] == "projectionElemSubslice"
                and len(projection[1]) == 3
                and projection[1][2] in {"true", "false"}
            ):
                head = application(
                    "subslice",
                    int_argument(projection[1][0]),
                    int_argument(projection[1][1]),
                    boolean(projection[1][2]),
                )
            elif (
                projection[0] == "projectionElemDowncast"
                and len(projection[1]) == 1
                and isinstance(projection[1][0], tuple)
                and projection[1][0][0] == "variantIdx"
                and len(projection[1][0][1]) == 1
            ):
                head = application(
                    "downcast", int_argument(projection[1][0][1][0])
                )
            elif projection[0] == "PointerOffset" and len(projection[1]) == 2:
                head = application(
                    "pointerOffset",
                    int_argument(projection[1][0]),
                    int_argument(projection[1][1]),
                )
            else:
                raise GateError(f"unsupported ProjectionElem: {projection}")
            result = application("projectionsCons", head, result)
        return result
    raise GateError(f"unsupported ProjectionElems: {term}")


def place(term: Any) -> str:
    if not isinstance(term, tuple) or term[0] != "place" or len(term[1]) != 2:
        raise GateError(f"unsupported Place: {term}")
    return application("place", int_argument(term[1][0]), projections(term[1][1]))


def typed_local(term: Any) -> str:
    if not isinstance(term, tuple):
        raise GateError(f"unsupported TypedLocal: {term}")
    if term[0] == "newLocal" and len(term[1]) == 2:
        return application("newLocal", ty(term[1][0]), mutability(term[1][1]))
    if term[0] == "typedValue" and len(term[1]) == 3:
        value = term[1][0]
        if value == "Moved":
            return application("movedLocal", ty(term[1][1]), mutability(term[1][2]))
        return application(
            "typedValue", mir_value(value), ty(term[1][1]), mutability(term[1][2])
        )
    raise GateError(f"unsupported TypedLocal: {term}")


def operand(term: Any) -> str:
    if not isinstance(term, tuple) or len(term[1]) != 1:
        raise GateError(f"unsupported Operand: {term}")
    if term[0] == "const":
        return application("constant", mir_value(term[1][0]))
    if term[0] == "operandConstant":
        constant = term[1][0]
        if not isinstance(constant, tuple) or constant[0] != "constOperand" or len(constant[1]) not in {2, 3}:
            raise GateError(f"unsupported constOperand: {constant}")
        span = constant[1][0]
        if not isinstance(span, tuple) or span[0] != "span" or len(span[1]) != 1:
            raise GateError(f"unsupported operand span: {span}")
        if len(constant[1]) == 3:
            user_ty, constant_value = constant[1][1:]
            if user_ty != "noUserTypeAnnotationIndex":
                raise GateError(f"unsupported operand user type: {user_ty}")
        else:
            constant_value = constant[1][1]
        if not isinstance(constant_value, tuple) or constant_value[0] != "mirConst" or len(constant_value[1]) != 3:
            raise GateError(f"unsupported operand mirConst: {constant_value}")
        kind, constant_ty, identifier = constant_value[1]
        if not isinstance(identifier, tuple) or identifier[0] != "mirConstId" or len(identifier[1]) != 1:
            raise GateError(f"unsupported operand mirConstId: {identifier}")
        if kind == "constantKindZeroSized":
            return application(
                "zeroSizedConstant",
                int_argument(span[1][0]),
                ty(constant_ty),
                int_argument(identifier[1][0]),
            )
        if not isinstance(kind, tuple) or kind[0] != "constantKindAllocated" or len(kind[1]) != 1:
            raise GateError(f"unsupported operand constant kind: {kind}")
        return application(
            "allocatedConstant",
            int_argument(span[1][0]),
            allocation(kind[1][0]),
            ty(constant_ty),
            int_argument(identifier[1][0]),
        )
    if term[0] == "copy":
        return application("copy", place(term[1][0]))
    if term[0] == "move":
        return application("move", place(term[1][0]))
    raise GateError(f"unsupported Operand: {term}")


def binary_op(term: Any) -> str:
    names = {
        "binOpAdd",
        "binOpAddUnchecked",
        "binOpSub",
        "binOpSubUnchecked",
        "binOpMul",
        "binOpMulUnchecked",
        "binOpDiv",
        "binOpRem",
        "binOpBitXor",
        "binOpBitAnd",
        "binOpBitOr",
        "binOpShl",
        "binOpShlUnchecked",
        "binOpShr",
        "binOpShrUnchecked",
        "binOpEq",
        "binOpLt",
        "binOpLe",
        "binOpNe",
        "binOpGe",
        "binOpGt",
        "binOpOffset",
    }
    if isinstance(term, str) and term in names:
        return application(term)
    raise GateError(f"unsupported BinaryOp: {term}")


def unary_op(term: Any) -> str:
    if isinstance(term, str) and term in {"unOpNot", "unOpNeg", "unOpPtrMetadata"}:
        return application(term)
    raise GateError(f"unsupported UnaryOp: {term}")


def nullary_op(term: Any) -> str:
    names = {
        "nullOpSizeOf": "sizeOf",
        "nullOpAlignOf": "alignOf",
        "nullOpUbChecks": "ubChecks",
    }
    if isinstance(term, str) and term in names:
        return application(names[term])
    raise GateError(f"unsupported NullOp: {term}")


def cast_kind(term: Any) -> str:
    if term == "castKindPtrToPtr":
        return application("ptrToPtr")
    if term == "castKindTransmute":
        return application("transmute")
    if (
        isinstance(term, tuple)
        and term[0] == "castKindPointerCoercion"
        and term[1] == ["pointerCoercionUnsize"]
    ):
        return application(
            "pointerCoercion", application("unsize")
        )
    raise GateError(f"unsupported CastKind: {term}")


def generic_arg(term: Any) -> str:
    if not isinstance(term, tuple) or len(term[1]) != 1:
        raise GateError(f"unsupported GenericArg: {term}")
    if term[0] == "genericArgKindLifetime":
        return application("genericArgLifetime", region(term[1][0]))
    if term[0] == "genericArgKindType":
        return application("genericArgType", ty(term[1][0]))
    if term[0] == "genericArgKindConst":
        return application("genericArgConst", ty_const(term[1][0]))
    raise GateError(f"unsupported GenericArg: {term}")


def generic_args(term: Any) -> str:
    if term == ".GenericArgs":
        items = []
    elif isinstance(term, tuple) and term[0] == "GenericArgs":
        items = term[1]
    else:
        raise GateError(f"unsupported GenericArgs: {term}")
    result = application("genericArgsEmpty")
    for item in reversed(items):
        result = application("genericArgsCons", generic_arg(item), result)
    return result


def aggregate_kind(term: Any) -> str:
    if term == "aggregateKindTuple":
        return application("aggregateTuple")
    if not isinstance(term, tuple):
        raise GateError(f"unsupported AggregateKind: {term}")
    if term[0] == "aggregateKindArray" and len(term[1]) == 1:
        return application("aggregateArray", ty(term[1][0]))
    if term[0] == "aggregateKindClosure" and len(term[1]) == 2:
        closure = term[1][0]
        if not isinstance(closure, tuple) or closure[0] != "closureDef" or len(closure[1]) != 1:
            raise GateError(f"unsupported ClosureDef: {closure}")
        return application(
            "aggregateClosure",
            application("closureDef", int_argument(closure[1][0])),
            generic_args(term[1][1]),
        )
    if term[0] == "aggregateKindRawPtr" and len(term[1]) == 2:
        return application(
            "aggregateRawPointer",
            ty(term[1][0]),
            mutability(term[1][1]),
        )
    if term[0] == "aggregateKindAdt" and len(term[1]) == 5:
        variant = term[1][1]
        if not isinstance(variant, tuple) or variant[0] != "variantIdx" or len(variant[1]) != 1:
            raise GateError(f"unsupported aggregate VariantIdx: {variant}")
        user_ty = term[1][3]
        if user_ty == "noUserTypeAnnotationIndex":
            parsed_user_ty = application("noUserTypeAnnotationIndex")
        elif isinstance(user_ty, tuple) and user_ty[0] == "someUserTypeAnnotationIndex" and len(user_ty[1]) == 1:
            index = user_ty[1][0]
            if not isinstance(index, tuple) or index[0] != "userTypeAnnotationIndex" or len(index[1]) != 1:
                raise GateError(f"unsupported UserTypeAnnotationIndex: {index}")
            parsed_user_ty = application("someUserTypeAnnotationIndex", int_argument(index[1][0]))
        else:
            raise GateError(f"unsupported MaybeUserTypeAnnotationIndex: {user_ty}")
        field = term[1][4]
        if field == "noFieldIdx":
            parsed_field = application("noFieldIdx")
        elif isinstance(field, tuple) and field[0] == "someFieldIdx" and len(field[1]) == 1:
            index = field[1][0]
            if not isinstance(index, tuple) or index[0] != "fieldIdx" or len(index[1]) != 1:
                raise GateError(f"unsupported FieldIdx: {index}")
            parsed_field = application("someFieldIdx", int_argument(index[1][0]))
        else:
            raise GateError(f"unsupported MaybeFieldIdx: {field}")
        return application(
            "aggregateAdt",
            adt_def(term[1][0]),
            int_argument(variant[1][0]),
            generic_args(term[1][2]),
            parsed_user_ty,
            parsed_field,
        )
    raise GateError(f"unsupported AggregateKind: {term}")


def rvalue(term: Any) -> str:
    if not isinstance(term, tuple):
        raise GateError(f"unsupported Rvalue: {term}")
    if term[0] == "rvalueUse" and len(term[1]) == 1:
        return application("use", operand(term[1][0]))
    if term[0] == "rvalueCast" and len(term[1]) == 3:
        return application(
            "cast", cast_kind(term[1][0]), operand(term[1][1]), ty(term[1][2])
        )
    if term[0] == "rvalueRef" and len(term[1]) == 3:
        return application(
            "ref", region(term[1][0]), borrow_kind(term[1][1]), place(term[1][2])
        )
    if term[0] == "rvalueAddressOf" and len(term[1]) == 2:
        return application(
            "addressOf", mutability(term[1][0]), place(term[1][1])
        )
    if term[0] == "rvalueUnaryOp" and len(term[1]) == 2:
        return application("unary", unary_op(term[1][0]), operand(term[1][1]))
    if term[0] == "rvalueNullaryOp" and len(term[1]) == 2:
        return application("nullary", nullary_op(term[1][0]), ty(term[1][1]))
    if term[0] == "rvalueBinaryOp" and len(term[1]) == 3:
        return application(
            "binary",
            binary_op(term[1][0]),
            operand(term[1][1]),
            operand(term[1][2]),
        )
    if term[0] == "rvalueCheckedBinaryOp" and len(term[1]) == 3:
        return application(
            "checkedBinary",
            binary_op(term[1][0]),
            operand(term[1][1]),
            operand(term[1][2]),
        )
    if term[0] == "rvalueAggregate" and len(term[1]) == 2:
        return application(
            "aggregateRvalue", aggregate_kind(term[1][0]), operands(term[1][1])
        )
    if term[0] == "rvalueRepeat" and len(term[1]) == 2:
        return application("repeat", operand(term[1][0]), ty_const(term[1][1]))
    if term[0] == "rvalueLen" and len(term[1]) == 1:
        return application("len", place(term[1][0]))
    if term[0] == "rvalueCopyForDeref" and len(term[1]) == 1:
        return application("copyForDeref", place(term[1][0]))
    if term[0] == "rvalueDiscriminant" and len(term[1]) == 1:
        return application("discriminantRvalue", place(term[1][0]))
    raise GateError(f"unsupported Rvalue: {term}")


def statement(term: Any) -> str:
    if isinstance(term, tuple) and term[0] == "assign" and len(term[1]) == 2:
        return application("assign", place(term[1][0]), rvalue(term[1][1]))
    raise GateError(f"unsupported Statement: {term}")


def statements(term: Any) -> str:
    items = term[1] if isinstance(term, tuple) and term[0] == ";" else [term]
    if not items or items[-1] != ".Statements":
        raise GateError(f"unsupported Statements: {term}")
    result = application("statementsEmpty")
    for item in reversed(items[:-1]):
        result = application("statementsCons", statement(item), result)
    return result


def branches(term: Any) -> str:
    if term == ".Branches":
        items = []
    elif isinstance(term, tuple) and term[0] == "Branches":
        items = term[1]
    else:
        raise GateError(f"unsupported Branches: {term}")
    result = application("branchesEmpty")
    for item in reversed(items):
        if not isinstance(item, tuple) or item[0] != "branch" or len(item[1]) != 2:
            raise GateError(f"unsupported Branch: {item}")
        branch = application(
            "branch", int_argument(item[1][0]), int_argument(item[1][1])
        )
        result = application("branchesCons", branch, result)
    return result


def switch_targets(term: Any) -> str:
    if not isinstance(term, tuple) or term[0] != "switchTargets" or len(term[1]) != 2:
        raise GateError(f"unsupported SwitchTargets: {term}")
    return application(
        "switchTargets", branches(term[1][0]), int_argument(term[1][1])
    )


def assert_message(term: Any) -> str:
    if isinstance(term, tuple) and term[0] == "assertMessageOverflow" and len(term[1]) == 3:
        return application(
            "overflow",
            binary_op(term[1][0]),
            operand(term[1][1]),
            operand(term[1][2]),
        )
    raise GateError(f"unsupported AssertMessage: {term}")


def unwind_action(term: Any) -> str:
    if term == "unwindActionContinue":
        return application("unwindContinue")
    raise GateError(f"unsupported UnwindAction: {term}")


def maybe_basic_block(term: Any) -> str:
    if term == "noBasicBlockIdx":
        return application("noBasicBlockIdx")
    if isinstance(term, tuple) and term[0] == "someBasicBlockIdx" and len(term[1]) == 1:
        return application("someBasicBlockIdx", int_argument(term[1][0]))
    raise GateError(f"unsupported MaybeBasicBlockIdx: {term}")


def operands(term: Any) -> str:
    if term == ".Operands":
        items = []
    elif isinstance(term, tuple) and term[0] == "Operands":
        items = term[1]
    else:
        raise GateError(f"unsupported Operands: {term}")
    result = application("operandsEmpty")
    for item in reversed(items):
        result = application("operandsCons", operand(item), result)
    return result


def local_decls(term: Any) -> str:
    if term == ".LocalDecls":
        items = []
    elif isinstance(term, tuple) and term[0] == "LocalDecls":
        items = term[1]
    else:
        raise GateError(f"unsupported LocalDecls: {term}")
    result = application("localDeclsEmpty")
    for item in reversed(items):
        if not isinstance(item, tuple) or item[0] != "localDecl" or len(item[1]) != 3:
            raise GateError(f"unsupported LocalDecl: {item}")
        span = item[1][1]
        if not isinstance(span, tuple) or span[0] != "span" or len(span[1]) != 1:
            raise GateError(f"unsupported local-declaration span: {span}")
        declaration = application(
            "localDecl",
            ty(item[1][0]),
            int_argument(span[1][0]),
            mutability(item[1][2]),
        )
        result = application("localDeclsCons", declaration, result)
    return result


def blocks(term: Any) -> str:
    if term == ".List":
        items = []
    elif isinstance(term, tuple) and term[0] == "List":
        items = term[1]
    else:
        raise GateError(f"unsupported function block list: {term}")
    result = application("'Stop'List")
    for item in reversed(items):
        entry = application(
            "ListItem",
            f"inj{{SortBasicBlock{{}},SortKItem{{}}}}({basic_block(item)})",
        )
        result = application("'Unds'List'Unds'", entry, result)
    return result


def function_body(term: Any) -> str:
    if not isinstance(term, tuple) or term[0] != "body" or len(term[1]) != 3:
        raise GateError(f"unsupported FunctionBody: {term}")
    return application(
        "body",
        blocks(term[1][0]),
        local_decls(term[1][1]),
        int_argument(term[1][2]),
    )


def function(term: Any) -> str:
    if not isinstance(term, tuple) or term[0] != "monoItemFn" or len(term[1]) != 2:
        raise GateError(f"unsupported Function: {term}")
    identifier, body = term[1]
    if not isinstance(identifier, tuple) or identifier[0] != "defId" or len(identifier[1]) != 1:
        raise GateError(f"unsupported function DefId: {identifier}")
    if not isinstance(body, tuple) or body[0] != "someBody" or len(body[1]) != 1:
        raise GateError(f"unsupported function body wrapper: {body}")
    return application(
        "monoItemFn",
        int_argument(identifier[1][0]),
        function_body(body[1][0]),
    )


def call_target(term: Any) -> str:
    if not isinstance(term, tuple) or term[0] != "operandConstant" or len(term[1]) != 1:
        raise GateError(f"unsupported CallTarget: {term}")
    constant = term[1][0]
    if not isinstance(constant, tuple) or constant[0] != "constOperand" or len(constant[1]) != 2:
        raise GateError(f"unsupported call constOperand: {constant}")
    span, constant_value = constant[1]
    if not isinstance(span, tuple) or span[0] != "span" or len(span[1]) != 1:
        raise GateError(f"unsupported call span: {span}")
    if not isinstance(constant_value, tuple) or constant_value[0] != "mirConst" or len(constant_value[1]) != 3:
        raise GateError(f"unsupported call mirConst: {constant_value}")
    zero_sized, function_ty, identifier = constant_value[1]
    if zero_sized != "constantKindZeroSized":
        raise GateError(f"unsupported call constant kind: {zero_sized}")
    if not isinstance(identifier, tuple) or identifier[0] != "mirConstId" or len(identifier[1]) != 1:
        raise GateError(f"unsupported call mirConstId: {identifier}")
    return application(
        "constantFunction",
        int_argument(span[1][0]),
        ty(function_ty),
        int_argument(identifier[1][0]),
    )


def terminator(term: Any) -> str:
    if term == "return":
        return application("return")
    if term == "terminatorKindUnreachable":
        return application("unreachable")
    if isinstance(term, tuple) and term[0] == "goto" and len(term[1]) == 1:
        return application("goto", int_argument(term[1][0]))
    if isinstance(term, tuple) and term[0] == "switchInt" and len(term[1]) == 2:
        return application("switchInt", operand(term[1][0]), switch_targets(term[1][1]))
    if isinstance(term, tuple) and term[0] == "assert" and len(term[1]) == 5:
        return application(
            "assert",
            operand(term[1][0]),
            boolean(term[1][1]),
            assert_message(term[1][2]),
            int_argument(term[1][3]),
            unwind_action(term[1][4]),
        )
    if (
        isinstance(term, tuple)
        and term[0] == "terminatorKindCall"
        and len(term[1]) == 5
    ):
        target = term[1][3]
        if not isinstance(target, tuple) or target[0] != "someBasicBlockIdx" or len(target[1]) != 1:
            raise GateError(f"unsupported call target block: {target}")
        return application(
            "call",
            call_target(term[1][0]),
            operands(term[1][1]),
            place(term[1][2]),
            int_argument(target[1][0]),
            unwind_action(term[1][4]),
        )
    if (
        isinstance(term, tuple)
        and term[0] == "terminatorKindDrop"
        and len(term[1]) == 3
    ):
        return application(
            "drop",
            place(term[1][0]),
            int_argument(term[1][1]),
            unwind_action(term[1][2]),
        )
    raise GateError(f"unsupported Terminator: {term}")


def basic_block(term: Any) -> str:
    if not isinstance(term, tuple) or term[0] != "basicBlock" or len(term[1]) != 2:
        raise GateError(f"unsupported BasicBlock: {term}")
    return application("block", statements(term[1][0]), terminator(term[1][1]))


def program(source: str) -> str:
    parser = Parser(source)
    blocks = []
    while parser.peek() == "ListItem":
        item = parser.term()
        if not isinstance(item, tuple) or len(item[1]) != 1:
            raise GateError(f"malformed ListItem: {item}")
        blocks.append(basic_block(item[1][0]))
    parser.take(".List")
    if parser.peek() is not None:
        raise GateError(f"unparsed Program suffix: {parser.tokens[parser.index:]}")
    result = application("'Stop'List")
    for block in reversed(blocks):
        item = application("ListItem", f"inj{{SortBasicBlock{{}},SortKItem{{}}}}({block})")
        result = application("'Unds'List'Unds'", item, result)
    return result


def locals_list(source: str) -> str:
    parser = Parser(source)
    entries = []
    while parser.peek() == "ListItem":
        item = parser.term()
        if not isinstance(item, tuple) or len(item[1]) != 1:
            raise GateError(f"malformed local ListItem: {item}")
        entries.append(typed_local(item[1][0]))
    parser.take(".List")
    if parser.peek() is not None:
        raise GateError(f"unparsed locals suffix: {parser.tokens[parser.index:]}")
    result = application("'Stop'List")
    for entry in reversed(entries):
        item = application("ListItem", f"inj{{SortTypedLocal{{}},SortKItem{{}}}}({entry})")
        result = application("'Unds'List'Unds'", item, result)
    return result


def stack_list(source: str) -> str:
    parser = Parser(source)
    frames = []
    while parser.peek() == "ListItem":
        item = parser.term()
        if not isinstance(item, tuple) or len(item[1]) != 1:
            raise GateError(f"malformed stack ListItem: {item}")
        frame = item[1][0]
        if not isinstance(frame, tuple) or frame[0] != "StackFrame" or len(frame[1]) != 6:
            raise GateError(f"unsupported StackFrame: {frame}")
        frame_span = frame[1][5]
        if not isinstance(frame_span, tuple) or frame_span[0] != "span" or len(frame_span[1]) != 1:
            raise GateError(f"unsupported stack-frame span: {frame_span}")
        frames.append(
            application(
                "stackFrame",
                ty(frame[1][0]),
                place(frame[1][1]),
                maybe_basic_block(frame[1][2]),
                unwind_action(frame[1][3]),
                locals_list_from_term(frame[1][4]),
                int_argument(frame_span[1][0]),
            )
        )
    parser.take(".List")
    if parser.peek() is not None:
        raise GateError(f"unparsed stack suffix: {parser.tokens[parser.index:]}")
    result = application("'Stop'List")
    for frame in reversed(frames):
        item = application("ListItem", f"inj{{SortStackFrame{{}},SortKItem{{}}}}({frame})")
        result = application("'Unds'List'Unds'", item, result)
    return result


def locals_list_from_term(term: Any) -> str:
    if term == ".List":
        entries = []
    elif isinstance(term, tuple) and term[0] == "List":
        entries = term[1]
    else:
        raise GateError(f"unsupported stack-frame locals: {term}")
    result = application("'Stop'List")
    for entry in reversed(entries):
        item = application(
            "ListItem",
            f"inj{{SortTypedLocal{{}},SortKItem{{}}}}({typed_local(entry)})",
        )
        result = application("'Unds'List'Unds'", item, result)
    return result


def functions_map(source: str) -> str:
    term = parse_term(source)
    if term == ".Map":
        items = []
    elif isinstance(term, tuple) and term[0] == "Map":
        items = term[1]
    else:
        raise GateError(f"unsupported function map: {term}")
    result = application("'Stop'Map")
    for key, value in items:
        entry = application(
            "'UndsPipe'-'-GT-Unds'",
            f"inj{{SortTy{{}},SortKItem{{}}}}({ty(key)})",
            f"inj{{SortFunction{{}},SortKItem{{}}}}({function(value)})",
        )
        result = application("'Unds'Map'Unds'", result, entry)
    return result


def types_map(source: str) -> str:
    term = parse_term(source)
    if term == ".Map":
        items = []
    elif isinstance(term, tuple) and term[0] == "Map":
        items = term[1]
    else:
        raise GateError(f"unsupported type map: {term}")
    result = application("'Stop'Map")
    for key, value in items:
        entry = application(
            "'UndsPipe'-'-GT-Unds'",
            f"inj{{SortTy{{}},SortKItem{{}}}}({ty(key)})",
            f"inj{{SortTypeInfo{{}},SortKItem{{}}}}({type_info(value)})",
        )
        result = application("'Unds'Map'Unds'", result, entry)
    return result


def memory_map(source: str) -> str:
    term = parse_term(source)
    if term == ".Map":
        items = []
    elif isinstance(term, tuple) and term[0] == "Map":
        items = term[1]
    else:
        raise GateError(f"unsupported allocation memory map: {term}")
    result = application("'Stop'Map")
    for key, value in items:
        entry = application(
            "'UndsPipe'-'-GT-Unds'",
            f"inj{{SortAllocId{{}},SortKItem{{}}}}({alloc_id(key)})",
            f"inj{{SortMirValue{{}},SortKItem{{}}}}({mir_value(value)})",
        )
        result = application("'Unds'Map'Unds'", result, entry)
    return result


def map_entry(name: str, sort: str, value: str) -> str:
    key = f'\\dv{{SortKConfigVar{{}}}}("${name}")'
    return application(
        "'UndsPipe'-'-GT-Unds'",
        f"inj{{SortKConfigVar{{}},SortKItem{{}}}}({key})",
        f"inj{{Sort{sort}{{}},SortKItem{{}}}}({value})",
    )


def initial_pattern(case: Mapping[str, Any]) -> str:
    current_func = parse_term(str(case.get("current_func", "ty(-1)")))
    caller = parse_term(str(case.get("caller", "ty(-1)")))
    destination = parse_term(
        str(case.get("destination", "place(local(-1), .ProjectionElems)"))
    )
    target = parse_term(str(case.get("target", "noBasicBlockIdx")))
    unwind = parse_term(str(case.get("unwind", "unwindActionContinue")))
    entries = (
        map_entry("PGM", "Command", application("run")),
        map_entry("PROGRAM", "List", program(str(case["program"]))),
        map_entry("LOCALS", "List", locals_list(str(case["locals"]))),
        map_entry("RETVAL", "RetVal", application("noReturn")),
        map_entry("CURRENTFUNC", "Ty", ty(current_func)),
        map_entry("CALLER", "Ty", ty(caller)),
        map_entry("DEST", "Place", place(destination)),
        map_entry("TARGET", "MaybeBasicBlockIdx", maybe_basic_block(target)),
        map_entry("UNWIND", "UnwindAction", unwind_action(unwind)),
        map_entry("STACK", "List", stack_list(str(case.get("stack", ".List")))),
        map_entry(
            "FUNCTIONS",
            "Map",
            functions_map(str(case.get("functions", ".Map"))),
        ),
        map_entry(
            "TYPES",
            "Map",
            types_map(str(case.get("types", ".Map"))),
        ),
        map_entry(
            "MEMORY",
            "Map",
            memory_map(str(case.get("memory", ".Map"))),
        ),
    )
    configuration = application("'Stop'Map")
    for entry in entries:
        configuration = application("'Unds'Map'Unds'", configuration, entry)
    return application("initGeneratedTopCell", configuration)


def applications(value: Any, name: str) -> list[Mapping[str, Any]]:
    found = []
    pending = [value]
    while pending:
        current = pending.pop()
        if isinstance(current, dict):
            if current.get("tag") == "App" and current.get("name") == name:
                found.append(current)
            pending.extend(current.values())
        elif isinstance(current, list):
            pending.extend(current)
    return found


def cell(state: Mapping[str, Any], name: str) -> Mapping[str, Any]:
    matches = applications(state, f"Lbl'-LT-'{name}'-GT-'")
    if len(matches) != 1:
        raise GateError(f"native result contains {len(matches)} <{name}> cells")
    arguments = matches[0].get("args")
    if not isinstance(arguments, list) or len(arguments) != 1 or not isinstance(arguments[0], dict):
        raise GateError(f"native <{name}> cell is malformed")
    return arguments[0]


def unwrap_injection(term: Mapping[str, Any]) -> Mapping[str, Any]:
    while term.get("tag") == "App" and term.get("name") == "inj":
        arguments = term.get("args")
        if not isinstance(arguments, list) or len(arguments) != 1 or not isinstance(arguments[0], dict):
            raise GateError(f"malformed sort injection: {term}")
        term = arguments[0]
    return term


def app_arguments(term: Mapping[str, Any], name: str, arity: int) -> list[Mapping[str, Any]]:
    arguments = term.get("args")
    if term.get("tag") != "App" or term.get("name") != f"Lbl{name}" or not isinstance(arguments, list) or len(arguments) != arity or not all(isinstance(item, dict) for item in arguments):
        raise GateError(f"expected {name}/{arity}: {term}")
    return arguments


def domain_value(term: Mapping[str, Any], sort_name: str) -> str:
    sort = term.get("sort")
    if term.get("tag") != "DV" or not isinstance(sort, dict) or sort.get("name") != f"Sort{sort_name}" or not isinstance(term.get("value"), str):
        raise GateError(f"expected concrete {sort_name}: {term}")
    return str(term["value"])


def rendered_mir_value(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    if term.get("name") == "Lblmoved":
        app_arguments(term, "moved", 0)
        return "Moved"
    if term.get("name") == "Lblinteger":
        value = app_arguments(term, "integer", 3)
        return (
            f"Integer({domain_value(value[0], 'Int')},"
            f"{domain_value(value[1], 'Int')},"
            f"{domain_value(value[2], 'Bool')})"
        )
    if term.get("name") == "Lblboolean":
        return f"BoolVal({domain_value(app_arguments(term, 'boolean', 1)[0], 'Bool')})"
    if term.get("name") == "Lblaggregate":
        value = app_arguments(term, "aggregate", 2)
        variant = domain_value(unwrap_injection(value[0]), "Int")
        fields = " ".join(
            f"ListItem({rendered_mir_value(field)})" for field in list_items(value[1])
        )
        prefix = f"{fields} " if fields else ""
        return f"Aggregate(variantIdx({variant}),{prefix}.List)"
    if term.get("name") == "Lblunion":
        value = app_arguments(term, "union", 2)
        field = domain_value(unwrap_injection(value[0]), "Int")
        return f"Union(fieldIdx({field}),{rendered_mir_value(value[1])})"
    if term.get("name") == "Lblrange":
        elements = " ".join(
            f"ListItem({rendered_mir_value(element)})"
            for element in list_items(app_arguments(term, "range", 1)[0])
        )
        suffix = f"{elements} " if elements else ""
        return f"Range({suffix}.List)"
    if term.get("name") == "Lblreference":
        value = app_arguments(term, "reference", 4)
        return (
            f"Reference({domain_value(unwrap_injection(value[0]), 'Int')},"
            f"{rendered_place(value[1])},{rendered_mutability(value[2])},"
            f"{rendered_metadata(value[3])})"
        )
    if term.get("name") == "Lblpointer":
        value = app_arguments(term, "pointer", 4)
        return (
            f"PtrLocal({domain_value(unwrap_injection(value[0]), 'Int')},"
            f"{rendered_place(value[1])},{rendered_mutability(value[2])},"
            f"{rendered_metadata(value[3])})"
        )
    if term.get("name") == "LblallocationReference":
        value = app_arguments(term, "allocationReference", 3)
        return (
            f"AllocRef({rendered_alloc_id(value[0])},"
            f"{rendered_projections(value[1])},{rendered_metadata(value[2])})"
        )
    raise GateError(f"unsupported concrete MirValue result: {term}")


def rendered_alloc_id(term: Mapping[str, Any]) -> str:
    value = app_arguments(unwrap_injection(term), "allocId", 1)
    return f"allocId({domain_value(unwrap_injection(value[0]), 'Int')})"


def rendered_binary_op(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    names = {
        "binOpAdd",
        "binOpAddUnchecked",
        "binOpSub",
        "binOpSubUnchecked",
        "binOpMul",
        "binOpMulUnchecked",
        "binOpDiv",
        "binOpRem",
        "binOpBitXor",
        "binOpBitAnd",
        "binOpBitOr",
        "binOpShl",
        "binOpShlUnchecked",
        "binOpShr",
        "binOpShrUnchecked",
        "binOpEq",
        "binOpLt",
        "binOpLe",
        "binOpNe",
        "binOpGe",
        "binOpGt",
    }
    name = str(term.get("name", ""))
    if name.startswith("Lbl") and name[3:] in names:
        rendered = name[3:]
        app_arguments(term, rendered, 0)
        return rendered
    raise GateError(f"unsupported concrete BinaryOp result: {term}")


def rendered_operand(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    if term.get("name") == "Lblconstant":
        value = app_arguments(term, "constant", 1)
        return f"const({rendered_mir_value(value[0])})"
    if term.get("name") in {"Lblcopy", "Lblmove"}:
        name = "copy" if term.get("name") == "Lblcopy" else "move"
        value = app_arguments(term, name, 1)
        return f"{name}({rendered_place(value[0])})"
    raise GateError(f"unsupported concrete Operand result: {term}")


def rendered_assert_message(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    value = app_arguments(term, "overflow", 3)
    return (
        f"assertMessageOverflow({rendered_binary_op(value[0])},"
        f"{rendered_operand(value[1])},{rendered_operand(value[2])})"
    )


def rendered_mir_error(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    if term.get("name") == "LblreachedUnreachable":
        app_arguments(term, "reachedUnreachable", 0)
        return "ReachedUnreachable"
    value = app_arguments(term, "assertError", 1)
    return f"AssertError({rendered_assert_message(value[0])})"


def list_items(term: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    name = term.get("name")
    arguments = term.get("args")
    if term.get("tag") == "App" and name == "Lbl'Stop'List" and arguments == []:
        return []
    if term.get("tag") == "App" and name == "Lbl'Unds'List'Unds'" and isinstance(arguments, list) and len(arguments) == 2 and all(isinstance(item, dict) for item in arguments):
        return list_items(arguments[0]) + list_items(arguments[1])
    if term.get("tag") == "App" and name == "LblListItem" and isinstance(arguments, list) and len(arguments) == 1 and isinstance(arguments[0], dict):
        return [arguments[0]]
    raise GateError(f"unsupported concrete List result: {term}")


def rendered_ty(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    return f"ty({domain_value(app_arguments(term, 'tyId', 1)[0], 'Int')})"


def rendered_mutability(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    if term.get("name") == "LblnotMutable":
        app_arguments(term, "notMutable", 0)
        return "mutabilityNot"
    if term.get("name") == "Lblmutable":
        app_arguments(term, "mutable", 0)
        return "mutabilityMut"
    raise GateError(f"unsupported concrete Mutability result: {term}")


def rendered_metadata_size(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    if term.get("name") == "LblnoMetadataSize":
        app_arguments(term, "noMetadataSize", 0)
        return "noMetadataSize"
    if term.get("name") in {"LblstaticSize", "LbldynamicSize"}:
        name = "staticSize" if term.get("name") == "LblstaticSize" else "dynamicSize"
        return f"{name}({domain_value(app_arguments(term, name, 1)[0], 'Int')})"
    raise GateError(f"unsupported concrete MetadataSize result: {term}")


def rendered_metadata(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    value = app_arguments(term, "metadata", 3)
    return (
        f"metadata({rendered_metadata_size(value[0])},"
        f"{domain_value(unwrap_injection(value[1]), 'Int')},"
        f"{rendered_metadata_size(value[2])})"
    )


def rendered_projection(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    if term.get("name") == "Lblderef":
        app_arguments(term, "deref", 0)
        return "projectionElemDeref"
    if term.get("name") == "Lblfield":
        value = app_arguments(term, "field", 2)
        return (
            f"projectionElemField(fieldIdx({domain_value(unwrap_injection(value[0]), 'Int')}),"
            f"{rendered_ty(value[1])})"
        )
    if term.get("name") == "Lblindex":
        value = app_arguments(term, "index", 1)
        return f"projectionElemIndex(local({domain_value(unwrap_injection(value[0]), 'Int')}))"
    if term.get("name") == "LblconstantIndex":
        value = app_arguments(term, "constantIndex", 3)
        return (
            f"projectionElemConstantIndex({domain_value(unwrap_injection(value[0]), 'Int')},"
            f"{domain_value(unwrap_injection(value[1]), 'Int')},"
            f"{domain_value(unwrap_injection(value[2]), 'Bool')})"
        )
    if term.get("name") == "Lblsubslice":
        value = app_arguments(term, "subslice", 3)
        return (
            f"projectionElemSubslice({domain_value(unwrap_injection(value[0]), 'Int')},"
            f"{domain_value(unwrap_injection(value[1]), 'Int')},"
            f"{domain_value(unwrap_injection(value[2]), 'Bool')})"
        )
    if term.get("name") == "Lbldowncast":
        value = app_arguments(term, "downcast", 1)
        return (
            "projectionElemDowncast(variantIdx("
            f"{domain_value(unwrap_injection(value[0]), 'Int')}))"
        )
    if term.get("name") == "LblpointerOffset":
        value = app_arguments(term, "pointerOffset", 2)
        return (
            f"PointerOffset({domain_value(unwrap_injection(value[0]), 'Int')},"
            f"{domain_value(unwrap_injection(value[1]), 'Int')})"
        )
    if term.get("name") == "LblsingletonArray":
        app_arguments(term, "singletonArray", 0)
        return "projectionElemSingletonArray"
    if term.get("name") == "LblwrapStruct":
        app_arguments(term, "wrapStruct", 0)
        return "projectionElemWrapStruct"
    if term.get("name") == "LbltoZst":
        app_arguments(term, "toZst", 0)
        return "projectionElemToZST"
    if term.get("name") == "LblfromZst":
        app_arguments(term, "fromZst", 0)
        return "projectionElemFromZST"
    raise GateError(f"unsupported concrete ProjectionElem result: {term}")


def rendered_projections(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    if term.get("name") == "LblprojectionsEmpty":
        app_arguments(term, "projectionsEmpty", 0)
        return ".ProjectionElems"
    value = app_arguments(term, "projectionsCons", 2)
    return f"{rendered_projection(value[0])} {rendered_projections(value[1])}"


def rendered_place(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    value = app_arguments(term, "place", 2)
    return (
        f"place(local({domain_value(unwrap_injection(value[0]), 'Int')}),"
        f"{rendered_projections(value[1])})"
    )


def rendered_typed_local(term: Mapping[str, Any]) -> str:
    term = unwrap_injection(term)
    if term.get("name") == "LblnewLocal":
        value = app_arguments(term, "newLocal", 2)
        return f"newLocal({rendered_ty(value[0])},{rendered_mutability(value[1])})"
    if term.get("name") == "LbltypedValue":
        value = app_arguments(term, "typedValue", 3)
        return f"typedValue({rendered_mir_value(value[0])},{rendered_ty(value[1])},{rendered_mutability(value[2])})"
    if term.get("name") == "LblmovedLocal":
        value = app_arguments(term, "movedLocal", 2)
        return f"typedValue(Moved,{rendered_ty(value[0])},{rendered_mutability(value[1])})"
    raise GateError(f"unsupported concrete TypedLocal result: {term}")


def rendered_locals(term: Mapping[str, Any]) -> str:
    items = [rendered_typed_local(value) for value in list_items(term)]
    return " ".join(f"ListItem({value})" for value in items) + " .List"


def normalize_term(value: str) -> str:
    value = re.sub(r"\s+", " ", value.strip())
    value = re.sub(r"\s*([(),;:])\s*", r"\1", value)
    return re.sub(r"\.\s+", ".", value)


def sole_state(result: Mapping[str, Any]) -> Mapping[str, Any]:
    leaves = result.get("leaves")
    if not isinstance(leaves, list) or len(leaves) != 1 or not isinstance(leaves[0], dict):
        raise GateError(f"native execution did not produce one leaf: {result}")
    state = leaves[0].get("state")
    if not isinstance(state, dict) or not isinstance(state.get("term"), dict):
        raise GateError(f"native execution leaf has no KORE state: {leaves[0]}")
    return state["term"]


def observed(case: Mapping[str, Any], result: Mapping[str, Any]) -> dict[str, Any]:
    state = sole_state(result)
    computation = cell(state, "k")
    blocks = applications(cell(state, "currentBody"), "LblListItem")
    outcome = {
        "id": str(case["id"]),
        "program": normalize_term(str(case["program"])),
        "block_count": len(blocks),
        "locals": normalize_term(rendered_locals(cell(state, "locals"))),
        "stack_depth": len(list_items(cell(state, "stack"))),
    }
    if "expected_error" in case:
        errors = applications(computation, "LblprogramError")
        if len(errors) != 1:
            raise GateError(f"{case['id']} contains {len(errors)} program errors")
        error = app_arguments(errors[0], "programError", 1)[0]
        if unwrap_injection(cell(state, "retVal")).get("name") != "LblnoReturn":
            raise GateError(f"{case['id']} unexpectedly returned after a program error")
        outcome["error"] = normalize_term(rendered_mir_error(error))
        outcome["return"] = "noReturn"
        return outcome
    if computation.get("name") != "dotk":
        raise GateError(f"{case['id']} did not halt")
    returned = app_arguments(cell(state, "retVal"), "returned", 1)[0]
    outcome["return"] = normalize_term(f"return({rendered_mir_value(returned)})")
    return outcome


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("runner", type=Path)
    parser.add_argument("definition", type=Path)
    parser.add_argument("module")
    parser.add_argument("corpus", type=Path)
    parser.add_argument(
        "--id",
        action="append",
        dest="case_ids",
        help="execute only the named behavior case; repeat to select several cases",
    )
    arguments = parser.parse_args()
    corpus = load_toml(arguments.corpus)
    cases = corpus.get("behavior")
    if not isinstance(cases, list) or not cases:
        raise GateError("behavior corpus is empty")
    if arguments.case_ids:
        requested = set(arguments.case_ids)
        cases = [case for case in cases if str(case.get("id")) in requested]
        found = {str(case["id"]) for case in cases}
        missing = requested - found
        if missing:
            raise GateError(f"unknown behavior case ids: {sorted(missing)}")
    requests = "".join(
        canonical_json({"id": str(case["id"]), "operation": "execute", "pattern": initial_pattern(case)}) + "\n"
        for case in cases
    )
    process = run([arguments.runner, arguments.definition, arguments.module], input=requests, timeout=600)
    responses = [json.loads(line) for line in process.stdout.splitlines()]
    if len(responses) != len(cases):
        raise GateError(f"native runner returned {len(responses)} responses for {len(cases)} requests")
    outcomes = []
    for case, response in zip(cases, responses, strict=True):
        if response.get("id") != case["id"] or not isinstance(response.get("result"), dict):
            raise GateError(f"native response order or shape differs: {response}")
        outcome = observed(case, response["result"])
        expected: dict[str, Any] = {
            "block_count": int(case["expected_block_count"]),
            "locals": normalize_term(str(case["expected_locals"])),
            "return": normalize_term(str(case["expected_return"])),
            "stack_depth": int(case.get("expected_stack_depth", 0)),
        }
        if "expected_error" in case:
            expected["error"] = normalize_term(str(case["expected_error"]))
        if {key: outcome[key] for key in expected} != expected:
            raise GateError(f"{case['id']} differs: expected={expected}, actual={outcome}")
        outcomes.append(outcome)
    digest = json_sha256(outcomes)
    print(f"PASS native KMIR behavior: {len(outcomes)} executions; sha256={digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
