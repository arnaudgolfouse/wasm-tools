/* Copyright 2018 Mozilla Foundation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use crate::limits::{
    MAX_WASM_FUNCTION_PARAMS, MAX_WASM_FUNCTION_RETURNS, MAX_WASM_STRUCT_FIELDS,
    MAX_WASM_SUPERTYPES,
};
use crate::{BinaryReader, BinaryReaderError, FromReader, Result, SectionLimited};
use std::fmt::{self, Debug, Write};

pub use wasm_types::{HeapType, RefType};

/// Represents the types of values in a WebAssembly module.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ValType {
    /// The value type is i32.
    I32,
    /// The value type is i64.
    I64,
    /// The value type is f32.
    F32,
    /// The value type is f64.
    F64,
    /// The value type is v128.
    V128,
    /// The value type is a reference.
    Ref(RefType),
}

/// Represents storage types introduced in the GC spec for array and struct fields.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum StorageType {
    /// The storage type is i8.
    I8,
    /// The storage type is i16.
    I16,
    /// The storage type is a value type.
    Val(ValType),
}

// The size of `ValType` is performance sensitive.
const _: () = {
    assert!(std::mem::size_of::<ValType>() == 4);
};

pub(crate) trait Inherits {
    fn inherits<'a, F>(&self, other: &Self, type_at: &F) -> bool
    where
        F: Fn(u32) -> &'a SubType;
}

impl From<RefType> for ValType {
    fn from(ty: RefType) -> ValType {
        ValType::Ref(ty)
    }
}

impl ValType {
    /// Alias for the wasm `funcref` type.
    pub const FUNCREF: ValType = ValType::Ref(RefType::FUNCREF);

    /// Alias for the wasm `externref` type.
    pub const EXTERNREF: ValType = ValType::Ref(RefType::EXTERNREF);

    /// Returns whether this value type is a "reference type".
    ///
    /// Only reference types are allowed in tables, for example, and with some
    /// instructions. Current reference types include `funcref` and `externref`.
    pub fn is_reference_type(&self) -> bool {
        matches!(self, ValType::Ref(_))
    }

    /// Whether the type is defaultable, i.e. it is not a non-nullable reference
    /// type.
    pub fn is_defaultable(&self) -> bool {
        match *self {
            Self::I32 | Self::I64 | Self::F32 | Self::F64 | Self::V128 => true,
            Self::Ref(rt) => rt.is_nullable(),
        }
    }

    pub(crate) fn is_valtype_byte(byte: u8) -> bool {
        match byte {
            0x7F | 0x7E | 0x7D | 0x7C | 0x7B | 0x70 | 0x6F | 0x6B | 0x6C | 0x6E | 0x65 | 0x69
            | 0x68 | 0x6D | 0x67 | 0x66 | 0x6A => true,
            _ => false,
        }
    }
}

impl Inherits for ValType {
    fn inherits<'a, F>(&self, other: &Self, type_at: &F) -> bool
    where
        F: Fn(u32) -> &'a SubType,
    {
        match (self, other) {
            (Self::Ref(r1), Self::Ref(r2)) => r1.inherits(r2, type_at),
            (
                s @ (Self::I32 | Self::I64 | Self::F32 | Self::F64 | Self::V128 | Self::Ref(_)),
                o,
            ) => s == o,
        }
    }
}

impl<'a> FromReader<'a> for StorageType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        match reader.peek()? {
            0x7A => {
                reader.position += 1;
                Ok(StorageType::I8)
            }
            0x79 => {
                reader.position += 1;
                Ok(StorageType::I16)
            }
            _ => Ok(StorageType::Val(reader.read()?)),
        }
    }
}

impl<'a> FromReader<'a> for ValType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        match reader.peek()? {
            0x7F => {
                reader.position += 1;
                Ok(ValType::I32)
            }
            0x7E => {
                reader.position += 1;
                Ok(ValType::I64)
            }
            0x7D => {
                reader.position += 1;
                Ok(ValType::F32)
            }
            0x7C => {
                reader.position += 1;
                Ok(ValType::F64)
            }
            0x7B => {
                reader.position += 1;
                Ok(ValType::V128)
            }
            0x70 | 0x6F | 0x6B | 0x6C | 0x6E | 0x65 | 0x69 | 0x68 | 0x6D | 0x67 | 0x66 | 0x6A => {
                Ok(ValType::Ref(reader.read()?))
            }
            _ => bail!(reader.original_position(), "invalid value type"),
        }
    }
}

impl fmt::Display for ValType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            ValType::I32 => "i32",
            ValType::I64 => "i64",
            ValType::F32 => "f32",
            ValType::F64 => "f64",
            ValType::V128 => "v128",
            ValType::Ref(r) => return fmt::Display::fmt(r, f),
        };
        f.write_str(s)
    }
}

// Static assert that we can fit indices up to `MAX_WASM_TYPES` inside `RefType`.
const _: () = {
    const fn can_roundtrip_index(index: u32) -> bool {
        assert!(RefType::can_represent_type_index(index));
        let rt = match RefType::indexed_func(true, index) {
            Some(rt) => rt,
            None => panic!(),
        };
        assert!(rt.is_nullable());
        let actual_index = match rt.type_index() {
            Some(i) => i,
            None => panic!(),
        };
        actual_index == index
    }

    assert!(can_roundtrip_index(crate::limits::MAX_WASM_TYPES as u32));
    assert!(can_roundtrip_index(0b00000000_00001111_00000000_00000000));
    assert!(can_roundtrip_index(0b00000000_00000000_11111111_00000000));
    assert!(can_roundtrip_index(0b00000000_00000000_00000000_11111111));
    assert!(can_roundtrip_index(0));
};

impl Inherits for RefType {
    fn inherits<'a, F>(&self, other: &Self, type_at: &F) -> bool
    where
        F: Fn(u32) -> &'a SubType,
    {
        self == other
            || ((other.is_nullable() || !self.is_nullable())
                && self.heap_type().inherits(&other.heap_type(), type_at))
    }
}

impl<'a> FromReader<'a> for RefType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        match reader.read()? {
            0x70 => Ok(RefType::FUNC.nullable()),
            0x6F => Ok(RefType::EXTERN.nullable()),
            0x6E => Ok(RefType::ANY.nullable()),
            0x65 => Ok(RefType::NONE.nullable()),
            0x69 => Ok(RefType::NOEXTERN.nullable()),
            0x68 => Ok(RefType::NOFUNC.nullable()),
            0x6D => Ok(RefType::EQ.nullable()),
            0x67 => Ok(RefType::STRUCT.nullable()),
            0x66 => Ok(RefType::ARRAY.nullable()),
            0x6A => Ok(RefType::I31.nullable()),
            byte @ (0x6B | 0x6C) => {
                let nullable = byte == 0x6C;
                let pos = reader.original_position();
                RefType::new(nullable, reader.read()?)
                    .ok_or_else(|| crate::BinaryReaderError::new("type index too large", pos))
            }
            _ => bail!(reader.original_position(), "malformed reference type"),
        }
    }
}

impl Inherits for HeapType {
    fn inherits<'a, F>(&self, other: &Self, type_at: &F) -> bool
    where
        F: Fn(u32) -> &'a SubType,
    {
        match (self, other) {
            (HeapType::Indexed(a), HeapType::Indexed(b)) => {
                a == b || type_at(*a).inherits(type_at(*b), type_at)
            }
            (HeapType::Indexed(a), HeapType::Func) => match type_at(*a).structural_type {
                StructuralType::Func(_) => true,
                _ => false,
            },
            (HeapType::Indexed(a), HeapType::Array) => match type_at(*a).structural_type {
                StructuralType::Array(_) => true,
                _ => false,
            },
            (HeapType::Indexed(a), HeapType::Struct) => match type_at(*a).structural_type {
                StructuralType::Struct(_) => true,
                _ => false,
            },
            (HeapType::Indexed(a), HeapType::Eq | HeapType::Any) => {
                match type_at(*a).structural_type {
                    StructuralType::Array(_) | StructuralType::Struct(_) => true,
                    _ => false,
                }
            }
            (HeapType::Eq, HeapType::Any) => true,
            (HeapType::I31 | HeapType::Array | HeapType::Struct, HeapType::Eq | HeapType::Any) => {
                true
            }
            (HeapType::None, HeapType::Indexed(a)) => match type_at(*a).structural_type {
                StructuralType::Array(_) | StructuralType::Struct(_) => true,
                _ => false,
            },
            (
                HeapType::None,
                HeapType::I31 | HeapType::Eq | HeapType::Any | HeapType::Array | HeapType::Struct,
            ) => true,
            (HeapType::NoExtern, HeapType::Extern) => true,
            (HeapType::NoFunc, HeapType::Func) => true,
            (HeapType::NoFunc, HeapType::Indexed(a)) => match type_at(*a).structural_type {
                StructuralType::Func(_) => true,
                _ => false,
            },
            (
                a @ (HeapType::Func
                | HeapType::Extern
                | HeapType::Any
                | HeapType::Indexed(_)
                | HeapType::None
                | HeapType::NoExtern
                | HeapType::NoFunc
                | HeapType::Eq
                | HeapType::Struct
                | HeapType::Array
                | HeapType::I31),
                b,
            ) => a == b,
        }
    }
}

impl<'a> FromReader<'a> for HeapType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        match reader.peek()? {
            0x70 => {
                reader.position += 1;
                Ok(HeapType::Func)
            }
            0x6F => {
                reader.position += 1;
                Ok(HeapType::Extern)
            }
            0x6E => {
                reader.position += 1;
                Ok(HeapType::Any)
            }
            0x65 => {
                reader.position += 1;
                Ok(HeapType::None)
            }
            0x69 => {
                reader.position += 1;
                Ok(HeapType::NoExtern)
            }
            0x68 => {
                reader.position += 1;
                Ok(HeapType::NoFunc)
            }
            0x6D => {
                reader.position += 1;
                Ok(HeapType::Eq)
            }
            0x67 => {
                reader.position += 1;
                Ok(HeapType::Struct)
            }
            0x66 => {
                reader.position += 1;
                Ok(HeapType::Array)
            }
            0x6A => {
                reader.position += 1;
                Ok(HeapType::I31)
            }
            _ => {
                let idx = match u32::try_from(reader.read_var_s33()?) {
                    Ok(idx) => idx,
                    Err(_) => {
                        bail!(reader.original_position(), "invalid indexed ref heap type");
                    }
                };
                Ok(HeapType::Indexed(idx))
            }
        }
    }
}

/// Represents a structural type in a WebAssembly module.
#[derive(Debug, Clone)]
pub enum StructuralType {
    /// The type is for a function.
    Func(FuncType),
    /// The type is for an array.
    Array(ArrayType),
    /// The type is for a struct.
    Struct(StructType),
}

/// Represents a subtype of possible other types in a WebAssembly module.
#[derive(Debug, Clone)]
pub struct SubType {
    /// Is the subtype final.
    pub is_final: bool,
    /// The list of supertype indexes. As of GC MVP, there can be at most one supertype.
    pub supertype_idx: Option<u32>,
    /// The structural type of the subtype.
    pub structural_type: StructuralType,
}

impl Inherits for SubType {
    fn inherits<'a, F>(&self, other: &Self, type_at: &F) -> bool
    where
        F: Fn(u32) -> &'a SubType,
    {
        !other.is_final
            && self
                .structural_type
                .inherits(&other.structural_type, type_at)
    }
}

/// Represents a type of a function in a WebAssembly module.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct FuncType {
    /// The combined parameters and result types.
    params_results: Box<[ValType]>,
    /// The number of parameter types.
    len_params: usize,
}

/// Represents a type of an array in a WebAssembly module.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct ArrayType(pub FieldType);

/// Represents a field type of an array or a struct.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct FieldType {
    /// Array element type.
    pub element_type: StorageType,
    /// Are elements mutable.
    pub mutable: bool,
}

/// Represents a type of a struct in a WebAssembly module.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct StructType {
    /// Struct fields.
    pub fields: Box<[FieldType]>,
}

impl Inherits for StructuralType {
    fn inherits<'a, F>(&self, other: &Self, type_at: &F) -> bool
    where
        F: Fn(u32) -> &'a SubType,
    {
        match (self, other) {
            (StructuralType::Func(a), StructuralType::Func(b)) => a.inherits(b, type_at),
            (StructuralType::Array(a), StructuralType::Array(b)) => a.inherits(b, type_at),
            (StructuralType::Struct(a), StructuralType::Struct(b)) => a.inherits(b, type_at),
            (StructuralType::Func(_), _) => false,
            (StructuralType::Array(_), _) => false,
            (StructuralType::Struct(_), _) => false,
        }
    }
}

impl Debug for FuncType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FuncType")
            .field("params", &self.params())
            .field("returns", &self.results())
            .finish()
    }
}

impl FuncType {
    /// Creates a new [`FuncType`] from the given `params` and `results`.
    pub fn new<P, R>(params: P, results: R) -> Self
    where
        P: IntoIterator<Item = ValType>,
        R: IntoIterator<Item = ValType>,
    {
        let mut buffer = params.into_iter().collect::<Vec<_>>();
        let len_params = buffer.len();
        buffer.extend(results);
        Self {
            params_results: buffer.into(),
            len_params,
        }
    }

    /// Creates a new [`FuncType`] fom its raw parts.
    ///
    /// # Panics
    ///
    /// If `len_params` is greater than the length of `params_results` combined.
    pub(crate) fn from_raw_parts(params_results: Box<[ValType]>, len_params: usize) -> Self {
        assert!(len_params <= params_results.len());
        Self {
            params_results,
            len_params,
        }
    }

    /// Returns a shared slice to the parameter types of the [`FuncType`].
    #[inline]
    pub fn params(&self) -> &[ValType] {
        &self.params_results[..self.len_params]
    }

    /// Returns a shared slice to the result types of the [`FuncType`].
    #[inline]
    pub fn results(&self) -> &[ValType] {
        &self.params_results[self.len_params..]
    }

    pub(crate) fn desc(&self) -> String {
        let mut s = String::new();
        s.push_str("[");
        for (i, param) in self.params().iter().enumerate() {
            if i > 0 {
                s.push_str(" ");
            }
            write!(s, "{param}").unwrap();
        }
        s.push_str("] -> [");
        for (i, result) in self.results().iter().enumerate() {
            if i > 0 {
                s.push_str(" ");
            }
            write!(s, "{result}").unwrap();
        }
        s.push_str("]");
        s
    }
}

impl Inherits for FuncType {
    fn inherits<'a, F>(&self, other: &Self, type_at: &F) -> bool
    where
        F: Fn(u32) -> &'a SubType,
    {
        self.params().len() == other.params().len()
            && self.results().len() == other.results().len()
            // Note: per GC spec, function subtypes are contravariant in their parameter types.
            // Also see https://en.wikipedia.org/wiki/Covariance_and_contravariance_(computer_science)
            && self
                .params()
                .iter()
                .zip(other.params())
                .fold(true, |r, (a, b)| r && b.inherits(a, type_at))
            && self
                .results()
                .iter()
                .zip(other.results())
                .fold(true, |r, (a, b)| r && a.inherits(b, type_at))
    }
}

impl Inherits for ArrayType {
    fn inherits<'a, F>(&self, other: &Self, type_at: &F) -> bool
    where
        F: Fn(u32) -> &'a SubType,
    {
        self.0.inherits(&other.0, type_at)
    }
}

impl Inherits for FieldType {
    fn inherits<'a, F>(&self, other: &Self, type_at: &F) -> bool
    where
        F: Fn(u32) -> &'a SubType,
    {
        (other.mutable || !self.mutable) && self.element_type.inherits(&other.element_type, type_at)
    }
}

impl Inherits for StorageType {
    fn inherits<'a, F>(&self, other: &Self, type_at: &F) -> bool
    where
        F: Fn(u32) -> &'a SubType,
    {
        match (self, other) {
            (Self::Val(a), Self::Val(b)) => a.inherits(b, type_at),
            (a @ (Self::I8 | Self::I16 | Self::Val(_)), b) => a == b,
        }
    }
}

impl Inherits for StructType {
    fn inherits<'a, F>(&self, other: &Self, type_at: &F) -> bool
    where
        F: Fn(u32) -> &'a SubType,
    {
        // Note: Structure types support width and depth subtyping.
        self.fields.len() >= other.fields.len()
            && self
                .fields
                .iter()
                .zip(other.fields.iter())
                .fold(true, |r, (a, b)| r && a.inherits(b, type_at))
    }
}

/// Represents a table's type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct TableType {
    /// The table's element type.
    pub element_type: RefType,
    /// Initial size of this table, in elements.
    pub initial: u32,
    /// Optional maximum size of the table, in elements.
    pub maximum: Option<u32>,
}

/// Represents a memory's type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct MemoryType {
    /// Whether or not this is a 64-bit memory, using i64 as an index. If this
    /// is false it's a 32-bit memory using i32 as an index.
    ///
    /// This is part of the memory64 proposal in WebAssembly.
    pub memory64: bool,

    /// Whether or not this is a "shared" memory, indicating that it should be
    /// send-able across threads and the `maximum` field is always present for
    /// valid types.
    ///
    /// This is part of the threads proposal in WebAssembly.
    pub shared: bool,

    /// Initial size of this memory, in wasm pages.
    ///
    /// For 32-bit memories (when `memory64` is `false`) this is guaranteed to
    /// be at most `u32::MAX` for valid types.
    pub initial: u64,

    /// Optional maximum size of this memory, in wasm pages.
    ///
    /// For 32-bit memories (when `memory64` is `false`) this is guaranteed to
    /// be at most `u32::MAX` for valid types. This field is always present for
    /// valid wasm memories when `shared` is `true`.
    pub maximum: Option<u64>,
}

impl MemoryType {
    /// Gets the index type for the memory.
    pub fn index_type(&self) -> ValType {
        if self.memory64 {
            ValType::I64
        } else {
            ValType::I32
        }
    }
}

/// Represents a global's type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct GlobalType {
    /// The global's type.
    pub content_type: ValType,
    /// Whether or not the global is mutable.
    pub mutable: bool,
}

/// Represents a tag kind.
#[derive(Clone, Copy, Debug)]
pub enum TagKind {
    /// The tag is an exception type.
    Exception,
}

/// A tag's type.
#[derive(Clone, Copy, Debug)]
pub struct TagType {
    /// The kind of tag
    pub kind: TagKind,
    /// The function type this tag uses.
    pub func_type_idx: u32,
}

/// A reader for the type section of a WebAssembly module.
pub type TypeSectionReader<'a> = SectionLimited<'a, SubType>;

impl<'a> FromReader<'a> for StructuralType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        read_structural_type(reader.read_u8()?, reader)
    }
}

fn read_structural_type(
    opcode: u8,
    reader: &mut BinaryReader,
) -> Result<StructuralType, BinaryReaderError> {
    Ok(match opcode {
        0x60 => StructuralType::Func(reader.read()?),
        0x5e => StructuralType::Array(reader.read()?),
        0x5f => StructuralType::Struct(reader.read()?),
        x => return reader.invalid_leading_byte(x, "type"),
    })
}

impl<'a> FromReader<'a> for SubType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        let pos = reader.original_position();
        Ok(match reader.read_u8()? {
            opcode @ (0x4e | 0x50) => {
                let idx_iter = reader.read_iter(MAX_WASM_SUPERTYPES, "supertype idxs")?;
                let idxs = idx_iter.collect::<Result<Vec<u32>>>()?;
                if idxs.len() > 1 {
                    return Err(BinaryReaderError::new(
                        "multiple supertypes not supported",
                        pos,
                    ));
                }
                SubType {
                    is_final: opcode == 0x4e,
                    supertype_idx: idxs.first().copied(),
                    structural_type: read_structural_type(reader.read_u8()?, reader)?,
                }
            }
            opcode => SubType {
                is_final: false,
                supertype_idx: None,
                structural_type: read_structural_type(opcode, reader)?,
            },
        })
    }
}

impl<'a> FromReader<'a> for FuncType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        let mut params_results = reader
            .read_iter(MAX_WASM_FUNCTION_PARAMS, "function params")?
            .collect::<Result<Vec<_>>>()?;
        let len_params = params_results.len();
        let results = reader.read_iter(MAX_WASM_FUNCTION_RETURNS, "function returns")?;
        params_results.reserve(results.size_hint().0);
        for result in results {
            params_results.push(result?);
        }
        Ok(FuncType::from_raw_parts(params_results.into(), len_params))
    }
}

impl<'a> FromReader<'a> for FieldType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        let element_type = reader.read()?;
        let mutable = reader.read_u8()?;
        Ok(FieldType {
            element_type,
            mutable: match mutable {
                0 => false,
                1 => true,
                _ => bail!(
                    reader.original_position(),
                    "invalid mutability byte for array type"
                ),
            },
        })
    }
}

impl<'a> FromReader<'a> for ArrayType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        Ok(ArrayType(FieldType::from_reader(reader)?))
    }
}

impl<'a> FromReader<'a> for StructType {
    fn from_reader(reader: &mut BinaryReader<'a>) -> Result<Self> {
        let fields = reader.read_iter(MAX_WASM_STRUCT_FIELDS, "struct fields")?;
        Ok(StructType {
            fields: fields.collect::<Result<_>>()?,
        })
    }
}
