use std::fmt;

/// A reference type.
///
/// The reference types proposal first introduced `externref` and `funcref`.
///
/// The function references proposal introduced typed function references.
///
/// The GC proposal introduces heap types: any, eq, i31, struct, array, nofunc, noextern, none.
//
// RefType is a bit-packed enum that fits in a `u24` aka `[u8; 3]`.
// Note that its content is opaque (and subject to change), but its API is stable.
// It has the following internal structure:
// ```
// [nullable:u1] [indexed==1:u1] [kind:u2] [index:u20]
// [nullable:u1] [indexed==0:u1] [type:u4] [(unused):u18]
// ```
// , where
// - `nullable` determines nullability of the ref
// - `indexed` determines if the ref is of a dynamically defined type with an index (encoded in a following bit-packing section) or of a known fixed type
// - `kind` determines what kind of indexed type the index is pointing to:
//   ```
//   10 = struct
//   11 = array
//   01 = function
//   ```
// - `index` is the type index
// - `type` is an enumeration of known types:
//   ```
//   1111 = any
//
//   1101 = eq
//   1000 = i31
//   1001 = struct
//   1100 = array
//
//   0101 = func
//   0100 = nofunc
//
//   0011 = extern
//   0010 = noextern
//
//   0000 = none
//   ```
// - `(unused)` is unused sequence of bits
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RefType([u8; 3]);

impl fmt::Debug for RefType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match (self.is_nullable(), self.heap_type()) {
            (true, HeapType::Any) => write!(f, "anyref"),
            (false, HeapType::Any) => write!(f, "(ref any)"),
            (true, HeapType::None) => write!(f, "nullref"),
            (false, HeapType::None) => write!(f, "(ref none)"),
            (true, HeapType::NoExtern) => write!(f, "nullexternref"),
            (false, HeapType::NoExtern) => write!(f, "(ref noextern)"),
            (true, HeapType::NoFunc) => write!(f, "nullfuncref"),
            (false, HeapType::NoFunc) => write!(f, "(ref nofunc)"),
            (true, HeapType::Eq) => write!(f, "eqref"),
            (false, HeapType::Eq) => write!(f, "(ref eq)"),
            (true, HeapType::Struct) => write!(f, "structref"),
            (false, HeapType::Struct) => write!(f, "(ref struct)"),
            (true, HeapType::Array) => write!(f, "arrayref"),
            (false, HeapType::Array) => write!(f, "(ref array)"),
            (true, HeapType::I31) => write!(f, "i31ref"),
            (false, HeapType::I31) => write!(f, "(ref i31)"),
            (true, HeapType::Extern) => write!(f, "externref"),
            (false, HeapType::Extern) => write!(f, "(ref extern)"),
            (true, HeapType::Func) => write!(f, "funcref"),
            (false, HeapType::Func) => write!(f, "(ref func)"),
            (true, HeapType::Indexed(idx)) => write!(f, "(ref null {idx})"),
            (false, HeapType::Indexed(idx)) => write!(f, "(ref {idx})"),
        }
    }
}

impl RefType {
    const NULLABLE_BIT: u32 = 1 << 23; // bit #23
    const INDEXED_BIT: u32 = 1 << 22; // bit #22

    const TYPE_MASK: u32 = 0b1111 << 18; // 4 bits #21-#18 (if `indexed == 0`)
    const ANY_TYPE: u32 = 0b1111 << 18;
    const EQ_TYPE: u32 = 0b1101 << 18;
    const I31_TYPE: u32 = 0b1000 << 18;
    const STRUCT_TYPE: u32 = 0b1001 << 18;
    const ARRAY_TYPE: u32 = 0b1100 << 18;
    const FUNC_TYPE: u32 = 0b0101 << 18;
    const NOFUNC_TYPE: u32 = 0b0100 << 18;
    const EXTERN_TYPE: u32 = 0b0011 << 18;
    const NOEXTERN_TYPE: u32 = 0b0010 << 18;
    const NONE_TYPE: u32 = 0b0000 << 18;

    const KIND_MASK: u32 = 0b11 << 20; // 2 bits #21-#20 (if `indexed == 1`)
    const STRUCT_KIND: u32 = 0b10 << 20;
    const ARRAY_KIND: u32 = 0b11 << 20;
    const FUNC_KIND: u32 = 0b01 << 20;

    const INDEX_MASK: u32 = (1 << 20) - 1; // 20 bits #19-#0 (if `indexed == 1`)

    /// A nullable untyped function reference aka `(ref null func)` aka
    /// `funcref` aka `anyfunc`.
    pub const FUNCREF: Self = RefType::FUNC.nullable();

    /// A nullable reference to an extern object aka `(ref null extern)` aka
    /// `externref`.
    pub const EXTERNREF: Self = RefType::EXTERN.nullable();

    /// A non-nullable untyped function reference aka `(ref func)`.
    pub const FUNC: Self = RefType::from_u32(Self::FUNC_TYPE);

    /// A non-nullable reference to an extern object aka `(ref extern)`.
    pub const EXTERN: Self = RefType::from_u32(Self::EXTERN_TYPE);

    /// A non-nullable reference to any object aka `(ref any)`.
    pub const ANY: Self = RefType::from_u32(Self::ANY_TYPE);

    /// A non-nullable reference to no object aka `(ref none)`.
    pub const NONE: Self = RefType::from_u32(Self::NONE_TYPE);

    /// A non-nullable reference to a noextern object aka `(ref noextern)`.
    pub const NOEXTERN: Self = RefType::from_u32(Self::NOEXTERN_TYPE);

    /// A non-nullable reference to a nofunc object aka `(ref nofunc)`.
    pub const NOFUNC: Self = RefType::from_u32(Self::NOFUNC_TYPE);

    /// A non-nullable reference to an eq object aka `(ref eq)`.
    pub const EQ: Self = RefType::from_u32(Self::EQ_TYPE);

    /// A non-nullable reference to a struct aka `(ref struct)`.
    pub const STRUCT: Self = RefType::from_u32(Self::STRUCT_TYPE);

    /// A non-nullable reference to an array aka `(ref array)`.
    pub const ARRAY: Self = RefType::from_u32(Self::ARRAY_TYPE);

    /// A non-nullable reference to an i31 object aka `(ref i31)`.
    pub const I31: Self = RefType::from_u32(Self::I31_TYPE);

    pub const fn can_represent_type_index(index: u32) -> bool {
        index & Self::INDEX_MASK == index
    }

    const fn u24_to_u32(bytes: [u8; 3]) -> u32 {
        let expanded_bytes = [bytes[0], bytes[1], bytes[2], 0];
        u32::from_le_bytes(expanded_bytes)
    }

    const fn u32_to_u24(x: u32) -> [u8; 3] {
        let bytes = x.to_le_bytes();
        debug_assert!(bytes[3] == 0);
        [bytes[0], bytes[1], bytes[2]]
    }

    #[inline]
    const fn as_u32(&self) -> u32 {
        Self::u24_to_u32(self.0)
    }

    #[inline]
    const fn from_u32(x: u32) -> Self {
        debug_assert!(x & (0b11111111 << 24) == 0);

        // if not indexed, type must be any/eq/i31/struct/array/func/extern/nofunc/noextern/none
        debug_assert!(
            x & Self::INDEXED_BIT != 0
                || matches!(
                    x & Self::TYPE_MASK,
                    Self::ANY_TYPE
                        | Self::EQ_TYPE
                        | Self::I31_TYPE
                        | Self::STRUCT_TYPE
                        | Self::ARRAY_TYPE
                        | Self::FUNC_TYPE
                        | Self::NOFUNC_TYPE
                        | Self::EXTERN_TYPE
                        | Self::NOEXTERN_TYPE
                        | Self::NONE_TYPE
                )
        );
        RefType(Self::u32_to_u24(x))
    }

    /// Create a reference to a typed function with the type at the given index.
    ///
    /// Returns `None` when the type index is beyond this crate's implementation
    /// limits and therefore is not representable.
    pub const fn indexed_func(nullable: bool, index: u32) -> Option<Self> {
        Self::indexed(nullable, Self::FUNC_KIND, index)
    }

    /// Create a reference to an array with the type at the given index.
    ///
    /// Returns `None` when the type index is beyond this crate's implementation
    /// limits and therefore is not representable.
    pub const fn indexed_array(nullable: bool, index: u32) -> Option<Self> {
        Self::indexed(nullable, Self::ARRAY_KIND, index)
    }

    /// Create a reference to a struct with the type at the given index.
    ///
    /// Returns `None` when the type index is beyond this crate's implementation
    /// limits and therefore is not representable.
    pub const fn indexed_struct(nullable: bool, index: u32) -> Option<Self> {
        Self::indexed(nullable, Self::STRUCT_KIND, index)
    }

    /// Create a reference to a user defined type at the given index.
    ///
    /// Returns `None` when the type index is beyond this crate's implementation
    /// limits and therefore is not representable, or when the heap type is not
    /// a typed array, struct or function.
    const fn indexed(nullable: bool, kind: u32, index: u32) -> Option<Self> {
        if Self::can_represent_type_index(index) {
            let nullable32 = Self::NULLABLE_BIT * nullable as u32;
            Some(RefType::from_u32(
                nullable32 | Self::INDEXED_BIT | kind | index,
            ))
        } else {
            None
        }
    }

    /// Create a new `RefType`.
    ///
    /// Returns `None` when the heap type's type index (if any) is beyond this
    /// crate's implementation limits and therfore is not representable.
    pub const fn new(nullable: bool, heap_type: HeapType) -> Option<Self> {
        let nullable32 = Self::NULLABLE_BIT * nullable as u32;
        match heap_type {
            HeapType::Indexed(index) => RefType::indexed(nullable, 0, index), // 0 bc we don't know the kind
            HeapType::Func => Some(Self::from_u32(nullable32 | Self::FUNC_TYPE)),
            HeapType::Extern => Some(Self::from_u32(nullable32 | Self::EXTERN_TYPE)),
            HeapType::Any => Some(Self::from_u32(nullable32 | Self::ANY_TYPE)),
            HeapType::None => Some(Self::from_u32(nullable32 | Self::NONE_TYPE)),
            HeapType::NoExtern => Some(Self::from_u32(nullable32 | Self::NOEXTERN_TYPE)),
            HeapType::NoFunc => Some(Self::from_u32(nullable32 | Self::NOFUNC_TYPE)),
            HeapType::Eq => Some(Self::from_u32(nullable32 | Self::EQ_TYPE)),
            HeapType::Struct => Some(Self::from_u32(nullable32 | Self::STRUCT_TYPE)),
            HeapType::Array => Some(Self::from_u32(nullable32 | Self::ARRAY_TYPE)),
            HeapType::I31 => Some(Self::from_u32(nullable32 | Self::I31_TYPE)),
        }
    }

    /// Is this a reference to a typed function?
    pub const fn is_typed_func_ref(&self) -> bool {
        self.is_indexed_type_ref() && self.as_u32() & Self::KIND_MASK == Self::FUNC_KIND
    }

    /// Is this a reference to an indexed type?
    pub const fn is_indexed_type_ref(&self) -> bool {
        self.as_u32() & Self::INDEXED_BIT != 0
    }

    /// If this is a reference to a typed function, get its type index.
    pub const fn type_index(&self) -> Option<u32> {
        if self.is_indexed_type_ref() {
            Some(self.as_u32() & Self::INDEX_MASK)
        } else {
            None
        }
    }

    /// Is this an untyped function reference aka `(ref null func)` aka `funcref` aka `anyfunc`?
    pub const fn is_func_ref(&self) -> bool {
        !self.is_indexed_type_ref() && self.as_u32() & Self::TYPE_MASK == Self::FUNC_TYPE
    }

    /// Is this a `(ref null extern)` aka `externref`?
    pub const fn is_extern_ref(&self) -> bool {
        !self.is_indexed_type_ref() && self.as_u32() & Self::TYPE_MASK == Self::EXTERN_TYPE
    }

    /// Is this ref type nullable?
    pub const fn is_nullable(&self) -> bool {
        self.as_u32() & Self::NULLABLE_BIT != 0
    }

    /// Get the non-nullable version of this ref type.
    pub const fn as_non_null(&self) -> Self {
        Self::from_u32(self.as_u32() & !Self::NULLABLE_BIT)
    }

    /// Get the non-nullable version of this ref type.
    pub const fn nullable(&self) -> Self {
        Self::from_u32(self.as_u32() | Self::NULLABLE_BIT)
    }

    /// Get the heap type that this is a reference to.
    pub fn heap_type(&self) -> HeapType {
        let s = self.as_u32();
        if self.is_indexed_type_ref() {
            HeapType::Indexed(self.type_index().unwrap())
        } else {
            match s & Self::TYPE_MASK {
                Self::FUNC_TYPE => HeapType::Func,
                Self::EXTERN_TYPE => HeapType::Extern,
                Self::ANY_TYPE => HeapType::Any,
                Self::NONE_TYPE => HeapType::None,
                Self::NOEXTERN_TYPE => HeapType::NoExtern,
                Self::NOFUNC_TYPE => HeapType::NoFunc,
                Self::EQ_TYPE => HeapType::Eq,
                Self::STRUCT_TYPE => HeapType::Struct,
                Self::ARRAY_TYPE => HeapType::Array,
                Self::I31_TYPE => HeapType::I31,
                _ => unreachable!(),
            }
        }
    }

    // Note that this is similar to `Display for RefType` except that it has
    // the indexes stubbed out.
    pub fn wat(&self) -> &'static str {
        match (self.is_nullable(), self.heap_type()) {
            (true, HeapType::Func) => "funcref",
            (true, HeapType::Extern) => "externref",
            (true, HeapType::Indexed(_)) => "(ref null $type)",
            (true, HeapType::Any) => "anyref",
            (true, HeapType::None) => "nullref",
            (true, HeapType::NoExtern) => "nullexternref",
            (true, HeapType::NoFunc) => "nullfuncref",
            (true, HeapType::Eq) => "eqref",
            (true, HeapType::Struct) => "structref",
            (true, HeapType::Array) => "arrayref",
            (true, HeapType::I31) => "i31ref",
            (false, HeapType::Func) => "(ref func)",
            (false, HeapType::Extern) => "(ref extern)",
            (false, HeapType::Indexed(_)) => "(ref $type)",
            (false, HeapType::Any) => "(ref any)",
            (false, HeapType::None) => "(ref none)",
            (false, HeapType::NoExtern) => "(ref noextern)",
            (false, HeapType::NoFunc) => "(ref nofunc)",
            (false, HeapType::Eq) => "(ref eq)",
            (false, HeapType::Struct) => "(ref struct)",
            (false, HeapType::Array) => "(ref array)",
            (false, HeapType::I31) => "(ref i31)",
        }
    }
}

impl fmt::Display for RefType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Note that this is similar to `RefType::wat` except that it has the
        // indexes filled out.
        let s = match (self.is_nullable(), self.heap_type()) {
            (true, HeapType::Func) => "funcref",
            (true, HeapType::Extern) => "externref",
            (true, HeapType::Indexed(i)) => return write!(f, "(ref null {i})"),
            (true, HeapType::Any) => "anyref",
            (true, HeapType::None) => "nullref",
            (true, HeapType::NoExtern) => "nullexternref",
            (true, HeapType::NoFunc) => "nullfuncref",
            (true, HeapType::Eq) => "eqref",
            (true, HeapType::Struct) => "structref",
            (true, HeapType::Array) => "arrayref",
            (true, HeapType::I31) => "i31ref",
            (false, HeapType::Func) => "(ref func)",
            (false, HeapType::Extern) => "(ref extern)",
            (false, HeapType::Indexed(i)) => return write!(f, "(ref {i})"),
            (false, HeapType::Any) => "(ref any)",
            (false, HeapType::None) => "(ref none)",
            (false, HeapType::NoExtern) => "(ref noextern)",
            (false, HeapType::NoFunc) => "(ref nofunc)",
            (false, HeapType::Eq) => "(ref eq)",
            (false, HeapType::Struct) => "(ref struct)",
            (false, HeapType::Array) => "(ref array)",
            (false, HeapType::I31) => "(ref i31)",
        };
        f.write_str(s)
    }
}

/// A heap type from function references. When the proposal is disabled, Index
/// is an invalid type.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HeapType {
    /// User defined type at the given index.
    Indexed(u32),
    /// Untyped (any) function.
    Func,
    /// External heap type.
    Extern,
    /// The `any` heap type. The common supertype (a.k.a. top) of all internal types.
    Any,
    /// The `none` heap type. The common subtype (a.k.a. bottom) of all internal types.
    None,
    /// The `noextern` heap type. The common subtype (a.k.a. bottom) of all external types.
    NoExtern,
    /// The `nofunc` heap type. The common subtype (a.k.a. bottom) of all function types.
    NoFunc,
    /// The `eq` heap type. The common supertype of all referenceable types on which comparison
    /// (ref.eq) is allowed.
    Eq,
    /// The `struct` heap type. The common supertype of all struct types.
    Struct,
    /// The `array` heap type. The common supertype of all array types.
    Array,
    /// The i31 heap type.
    I31,
}
