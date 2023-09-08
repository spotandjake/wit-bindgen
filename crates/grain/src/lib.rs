use std::{
    collections::{HashMap, HashSet},
    mem,
};

use heck::*;
use wit_bindgen_core::{
    wit_parser::{
        self, Flags, FlagsRepr, Function, Int, InterfaceId, Resolve, Result_, SizeAlign, Tuple,
        Type, TypeDef, TypeDefKind, TypeId, WorldId, WorldKey,
    },
    Files, InterfaceGenerator, Source, WorldGenerator,
};

use heck::{ToLowerCamelCase, ToUpperCamelCase};

#[derive(Default, Debug, Clone)]
#[cfg_attr(feature = "clap", derive(clap::Args))]
pub struct Opts {}

impl Opts {
    pub fn build(&self) -> Box<dyn WorldGenerator> {
        Box::new(Grain {
            _opts: self.clone(),
            ..Grain::default()
        })
    }
}

#[derive(Default)]
pub struct Grain {
    _opts: Opts,
    src: Source,
    world: String,
    sizes: SizeAlign,
    interface_names: HashMap<InterfaceId, WorldKey>,

    // Interfaces who have had their types printed.
    //
    // This is used to guard against printing the types for an interface twice.
    // The same interface can be both imported and exported in which case only
    // one set of types is generated and all bindings for both imports and
    // exports use that set of types.
    interfaces_with_types_printed: HashSet<InterfaceId>,
    return_pointer_area_size: usize,
}

impl Grain {
    fn interface<'a>(
        &'a mut self,
        resolve: &'a Resolve,
        name: &'a Option<&'a WorldKey>,
        in_import: bool,
    ) -> GrainInterfaceGenerator<'a> {
        GrainInterfaceGenerator {
            src: Source::default(),
            gen: self,
            resolve,
            interface: None,
            name,
            in_import,
            export_funcs: Vec::new(),
        }
    }

    // fn finish_types(&mut self, resolve: &Resolve) {
    //     for (id, _) in resolve.types.iter() {
    //         if let Some((_, ty)) = self.types.get(&id) {
    //             self.src.push_str(&ty);
    //         }
    //     }
    // }
}

impl WorldGenerator for Grain {
    fn preprocess(&mut self, resolve: &Resolve, world: WorldId) {
        let name = &resolve.worlds[world].name;
        self.world = name.to_string();
        self.sizes.fill(resolve);
    }
    fn import_interface(
        &mut self,
        resolve: &Resolve,
        name: &WorldKey,
        id: InterfaceId,
        _files: &mut Files,
    ) {
        let name_raw = &resolve.name_world_key(name);
        self.src
            .push_str(&format!("// Import functions from {name_raw}\n"));
        self.interface_names.insert(id, name.clone());

        let binding = Some(name);
        let mut gen = self.interface(resolve, &binding, true);
        gen.interface = Some(id);
        if gen.gen.interfaces_with_types_printed.insert(id) {
            gen.types(id);
        }

        for (_name, func) in resolve.interfaces[id].functions.iter() {
            gen.import(resolve, func);
        }
        gen.finish();

        let src = mem::take(&mut gen.src);
        self.src.push_str(&src);
    }
    fn import_funcs(
        &mut self,
        resolve: &Resolve,
        world: WorldId,
        funcs: &[(&str, &Function)],
        _files: &mut Files,
    ) {
        let name = &resolve.worlds[world].name;
        self.src
            .push_str(&format!("// Import functions from {name}\n"));

        let mut gen = self.interface(resolve, &None, true);
        for (_name, func) in funcs.iter() {
            gen.import(resolve, func);
        }
        gen.finish();

        let src = mem::take(&mut gen.src);
        self.src.push_str(&src);
    }

    fn import_types(
        &mut self,
        resolve: &Resolve,
        world: WorldId,
        types: &[(&str, TypeId)],
        _files: &mut Files,
    ) {
        let mut gen = self.interface(resolve, &None, false);
        for (name, id) in types {
            gen.define_type(name, *id);
        }
        gen.finish();
        let src = mem::take(&mut gen.src);
        self.src.push_str(&src);
    }

    fn export_funcs(
        &mut self,
        resolve: &Resolve,
        world: WorldId,
        funcs: &[(&str, &Function)],
        _files: &mut Files,
    ) -> anyhow::Result<()> {
        let name = &resolve.worlds[world].name;
        self.src
            .push_str(&format!("// Export functions from {name}\n"));

        let mut gen = self.interface(resolve, &None, false);
        for (_name, func) in funcs.iter() {
            gen.export(resolve, func);
        }

        gen.finish();

        let src = mem::take(&mut gen.src);
        self.src.push_str(&src);
        Ok(())
    }

    fn export_interface(
        &mut self,
        resolve: &Resolve,
        name: &WorldKey,
        id: InterfaceId,
        _files: &mut Files,
    ) -> anyhow::Result<()> {
        self.interface_names.insert(id, name.clone());
        let name_raw = &resolve.name_world_key(name);
        self.src
            .push_str(&format!("// Export functions from {name_raw}\n"));

        let binding = Some(name);
        let mut gen = self.interface(resolve, &binding, false);
        gen.interface = Some(id);
        if gen.gen.interfaces_with_types_printed.insert(id) {
            gen.types(id);
        }

        for (_name, func) in resolve.interfaces[id].functions.iter() {
            gen.export(resolve, func);
        }

        gen.finish();

        let src = mem::take(&mut gen.src);
        self.src.push_str(&src);
        Ok(())
    }

    fn finish(&mut self, resolve: &Resolve, world: WorldId, files: &mut Files) {
        let world = &resolve.worlds[world];
        let mut full_src = Source::default();

        full_src.push_str(&format!("module {}\n\n", world.name.to_upper_camel_case()));

        // TODO: Selectively include only used libraries
        full_src.push_str("include \"runtime/dataStructures\" as DataStructures\n");
        full_src.push_str("include \"runtime/unsafe/wasmi32\" as WasmI32\n");
        full_src.push_str("include \"runtime/unsafe/wasmi64\" as WasmI64\n");
        full_src.push_str("include \"runtime/unsafe/wasmf32\" as WasmF32\n");
        full_src.push_str("include \"runtime/unsafe/wasmf64\" as WasmF64\n");
        full_src.push_str("include \"runtime/unsafe/memory\" as Memory\n");
        full_src.push_str("include \"int32\" as Int32\n");
        full_src.push_str("include \"int64\" as Int64\n");
        full_src.push_str("include \"char\" as Char\n");
        full_src.push_str("include \"list\" as List\n");

        full_src.push_str("\n");

        if self.return_pointer_area_size > 0 {
            full_src.push_str("@unsafe\n");
            full_src.push_str(&format!(
                "let _RET_AREA = Memory.malloc({}n)\n\n",
                self.return_pointer_area_size
            ));
        }

        full_src.push_str(self.src.as_mut_string());

        files.push(
            &format!("{}.gr", world.name.to_lower_camel_case()),
            full_src.as_bytes(),
        );
    }
}

struct GrainInterfaceGenerator<'a> {
    src: Source,
    gen: &'a mut Grain,
    resolve: &'a Resolve,
    interface: Option<InterfaceId>,
    name: &'a Option<&'a WorldKey>,
    in_import: bool,
    export_funcs: Vec<(String, String)>,
}

impl GrainInterfaceGenerator<'_> {
    pub fn is_empty_type(&mut self, ty: &TypeDef) -> bool {
        match &ty.kind {
            TypeDefKind::Type(t) => {
                let def = match t {
                    Type::Id(id) => &self.resolve().types[*id],
                    _ => return false,
                };
                self.is_empty_type(def)
            }
            TypeDefKind::Record(r) => r.fields.is_empty(),
            TypeDefKind::Tuple(t) => t.types.is_empty(),
            _ => false,
        }
    }

    fn print_tydef(&mut self, ty: &TypeDefKind) {
        match ty {
            TypeDefKind::Type(t) => self.print_ty(t),
            TypeDefKind::List(Type::Char) => self.src.push_str("String"),
            TypeDefKind::List(Type::U8) => self.src.push_str("Bytes"),
            TypeDefKind::List(t) => {
                self.src.push_str("List<");
                self.print_ty(t);
                self.src.push_str(">");
            }
            TypeDefKind::Option(t) => {
                self.src.push_str("Option<");
                self.print_ty(t);
                self.src.push_str(">");
            }
            TypeDefKind::Result(Result_ { ok, err }) => {
                self.src.push_str("Result<");
                match ok {
                    Some(ty) => self.print_ty(ty),
                    None => self.src.push_str("Void"),
                }
                self.src.push_str(", ");
                match err {
                    Some(ty) => self.print_ty(ty),
                    None => self.src.push_str("Void"),
                }
                self.src.push_str(">");
            }
            TypeDefKind::Tuple(Tuple { types }) => {
                if types.len() == 0 {
                    // Grain does not have zero-length tuples
                    self.src.push_str("Void");
                    return;
                }
                self.src.push_str("(");
                let singleton = types.len() == 1;
                for (i, ty) in types.iter().enumerate() {
                    self.print_ty(ty);
                    if singleton || i != types.len() - 1 {
                        self.src.push_str(", ");
                    }
                }
                self.src.push_str(")");
            }
            _ => {
                unreachable!()
            }
        }
    }

    fn print_ty(&mut self, ty: &Type) {
        match ty {
            Type::Bool => self.src.push_str("Bool"),
            Type::U8 => self.src.push_str("Uint8"),
            Type::S8 => self.src.push_str("Int8"),
            Type::U16 => self.src.push_str("Uint16"),
            Type::S16 => self.src.push_str("Int16"),
            Type::U32 => self.src.push_str("Uint32"),
            Type::S32 => self.src.push_str("Int32"),
            Type::U64 => self.src.push_str("Uint64"),
            Type::S64 => self.src.push_str("Int64"),
            Type::Float32 => self.src.push_str("Float32"),
            Type::Float64 => self.src.push_str("Float64"),
            Type::Char => self.src.push_str("Char"),
            Type::String => self.src.push_str("String"),
            Type::Id(id) => {
                let types = &self.resolve().types;
                let ty = &types[*id];
                if self.is_empty_type(&ty) {
                    self.src.push_str("Void");
                    return;
                }
                let ty = &types[*id];
                if let Some(name) = &ty.name {
                    self.src.push_str(&name.to_upper_camel_case());
                    return;
                }
                self.print_tydef(&ty.kind);
            }
        }
    }

    fn print_func_signature(&mut self, resolve: &Resolve, func: &Function) {
        todo!()
    }

    fn import(&mut self, resolve: &Resolve, func: &Function) {
        let mut func_bindgen = FunctionBindgen::new(self, func);
        // lower params to c
        func.params.iter().for_each(|(name, ty)| {
            func_bindgen.lower(&name, ty, false);
        });
        // lift results from c
        match func.results.len() {
            0 => {}
            1 => {
                let ty = func.results.iter_types().next().unwrap();
                func_bindgen.lift("ret", ty);
            }
            _ => {
                for (i, ty) in func.results.iter_types().enumerate() {
                    func_bindgen.lift(&format!("ret{i}"), ty);
                }
            }
        };

        let lowered_args = func_bindgen.lowered_args;
        let ret = func_bindgen.lifted_args;
        let lowered_src = func_bindgen.lowered_src.to_string();
        let lifted_src = func_bindgen.lifted_src.to_string();

        // print function signature
        self.print_func_signature(resolve, func);

        // body
        // prepare args
        self.src.push_str(lowered_src.as_str());

        self.import_invoke(resolve, func, lowered_args, &lifted_src, ret);

        // return

        // self.src.push_str("}\n\n");
    }

    fn import_invoke(
        &mut self,
        resolve: &Resolve,
        func: &Function,
        lowered_args: Vec<String>,
        lift_src: &str,
        ret: Vec<String>,
    ) {
        todo!()
    }

    fn export(&mut self, resolve: &Resolve, func: &Function) {
        todo!()
    }

    fn finish(&mut self) {
        // todo!()
    }
}

impl<'a> InterfaceGenerator<'a> for GrainInterfaceGenerator<'a> {
    fn resolve(&self) -> &'a Resolve {
        self.resolve
    }

    fn type_record(
        &mut self,
        id: TypeId,
        name: &str,
        record: &wit_parser::Record,
        docs: &wit_parser::Docs,
    ) {
        if record.fields.is_empty() {
            // Empty records don't exist in Grain
            self.src.push_str(&format!(
                "provide type {r} = Void\n",
                r = name.to_upper_camel_case()
            ));
            return;
        }

        self.src.push_str(&format!(
            "provide record {r} {{",
            r = name.to_upper_camel_case()
        ));
        for (_i, field) in record.fields.iter().enumerate() {
            self.src
                .push_str(&format!("\n{f}: ", f = to_grain_ident(&field.name)));
            self.print_ty(&field.ty);
            self.src.push_str(",");
        }
        self.src.push_str("\n}")
    }

    fn type_resource(&mut self, id: TypeId, name: &str, docs: &wit_parser::Docs) {
        todo!()
    }

    fn type_flags(&mut self, id: TypeId, name: &str, flags: &Flags, docs: &wit_parser::Docs) {
        let typename = name.to_lower_camel_case();
        let ty = int_repr(flags_repr(flags));
        self.src
            .push_str(&format!("provide type {typename} = {ty}\n\n"));
        let repr = flags_repr(flags);
        for (i, field) in flags.flags.iter().enumerate() {
            self.src.push_str(&format!(
                "provide let _{}_{}: {typename} = {}.shl(1{}, {}{})\n",
                name.to_shouty_snake_case(),
                field.name.to_shouty_snake_case(),
                int_repr(repr),
                int_suffix(repr),
                i,
                int_suffix(repr),
            ));
        }
        self.src.push_str("\n");
    }

    fn type_tuple(
        &mut self,
        _id: TypeId,
        _name: &str,
        _flags: &wit_parser::Tuple,
        _docs: &wit_parser::Docs,
    ) {
        // No type needed
    }

    fn type_variant(
        &mut self,
        id: TypeId,
        name: &str,
        variant: &wit_parser::Variant,
        docs: &wit_parser::Docs,
    ) {
        todo!()
    }

    fn type_option(&mut self, _id: TypeId, _name: &str, _payload: &Type, _docs: &wit_parser::Docs) {
        // No type needed
    }

    fn type_result(
        &mut self,
        id: TypeId,
        name: &str,
        result: &wit_parser::Result_,
        docs: &wit_parser::Docs,
    ) {
        todo!()
    }

    fn type_enum(
        &mut self,
        id: TypeId,
        name: &str,
        enum_: &wit_parser::Enum,
        docs: &wit_parser::Docs,
    ) {
        todo!()
    }

    fn type_alias(&mut self, id: TypeId, name: &str, ty: &Type, docs: &wit_parser::Docs) {
        todo!()
    }

    fn type_list(&mut self, id: TypeId, name: &str, ty: &Type, docs: &wit_parser::Docs) {
        todo!()
    }

    fn type_builtin(&mut self, id: TypeId, name: &str, ty: &Type, docs: &wit_parser::Docs) {
        todo!()
    }
}

struct FunctionBindgen<'a, 'b> {
    interface: &'a mut GrainInterfaceGenerator<'b>,
    _func: &'a Function,
    lowered_args: Vec<String>,
    lifted_args: Vec<String>,
    lowered_src: Source,
    lifted_src: Source,
}

impl<'a, 'b> FunctionBindgen<'a, 'b> {
    fn new(interface: &'a mut GrainInterfaceGenerator<'b>, func: &'a Function) -> Self {
        Self {
            interface,
            _func: func,
            lowered_args: Default::default(),
            lifted_args: Default::default(),
            lowered_src: Default::default(),
            lifted_src: Default::default(),
        }
    }

    fn lower(&mut self, name: &str, ty: &Type, in_export: bool) {
        match ty {
            Type::Bool => self.lower_bool(),
            Type::U8 => self.lower_u8(),
            Type::U16 => self.lower_u16(),
            Type::U32 => self.lower_u32(),
            Type::U64 => self.lower_u64(),
            Type::S8 => self.lower_s8(),
            Type::S16 => self.lower_s16(),
            Type::S32 => self.lower_s32(),
            Type::S64 => self.lower_s64(),
            Type::Float32 => self.lower_f32(),
            Type::Float64 => self.lower_f64(),
            Type::Char => self.lower_char(),
            Type::String => self.lower_string(),
            Type::Id(_) => self.lower_id(),
        };
    }

    fn lift(&mut self, name: &str, ty: &Type) {
        match ty {
            Type::Bool => self.lift_bool(),
            Type::U8 => self.lift_u8(),
            Type::U16 => self.lift_u16(),
            Type::U32 => self.lift_u32(),
            Type::U64 => self.lift_u64(),
            Type::S8 => self.lift_s8(),
            Type::S16 => self.lift_s16(),
            Type::S32 => self.lift_s32(),
            Type::S64 => self.lift_s64(),
            Type::Float32 => self.lift_f32(),
            Type::Float64 => self.lift_f64(),
            Type::Char => self.lift_char(),
            Type::String => self.lift_string(),
            Type::Id(_) => self.lift_id(),
        }
    }

    fn lower_bool(&self) {
        todo!()
    }

    fn lower_u8(&self) {
        todo!()
    }

    fn lower_u16(&self) {
        todo!()
    }

    fn lower_u32(&self) {
        todo!()
    }

    fn lower_u64(&self) {
        todo!()
    }

    fn lower_s8(&self) {
        todo!()
    }

    fn lower_s16(&self) {
        todo!()
    }

    fn lower_s32(&self) {
        todo!()
    }

    fn lower_s64(&self) {
        todo!()
    }

    fn lower_f32(&self) {
        todo!()
    }

    fn lower_f64(&self) {
        todo!()
    }

    fn lower_char(&self) {
        todo!()
    }

    fn lower_string(&self) {
        todo!()
    }

    fn lower_id(&self) {
        todo!()
    }

    fn lift_bool(&self) {
        todo!()
    }

    fn lift_u8(&self) {
        todo!()
    }

    fn lift_u16(&self) {
        todo!()
    }

    fn lift_u32(&self) {
        todo!()
    }

    fn lift_u64(&self) {
        todo!()
    }

    fn lift_s8(&self) {
        todo!()
    }

    fn lift_s16(&self) {
        todo!()
    }

    fn lift_s32(&self) {
        todo!()
    }

    fn lift_s64(&self) {
        todo!()
    }

    fn lift_f32(&self) {
        todo!()
    }

    fn lift_f64(&self) {
        todo!()
    }

    fn lift_char(&self) {
        todo!()
    }

    fn lift_string(&self) {
        todo!()
    }

    fn lift_id(&self) {
        todo!()
    }
}

fn int_repr(repr: Int) -> &'static str {
    match repr {
        Int::U8 => "Int32",
        Int::U16 => "Int32",
        Int::U32 => "Int32",
        Int::U64 => "Int64",
    }
}

fn flags_repr(f: &Flags) -> Int {
    match f.repr() {
        FlagsRepr::U8 => Int::U8,
        FlagsRepr::U16 => Int::U16,
        FlagsRepr::U32(1) => Int::U32,
        FlagsRepr::U32(2) => Int::U64,
        repr => panic!("unimplemented flags {:?}", repr),
    }
}

fn int_suffix(repr: Int) -> &'static str {
    match repr {
        Int::U8 => "l",
        Int::U16 => "l",
        Int::U32 => "l",
        Int::U64 => "L",
    }
}

fn to_grain_ident(name: &str) -> String {
    match name {
        "assert" => "assert_".into(),
        "break" => "break_".into(),
        "continue" => "continue_".into(),
        "else" => "else_".into(),
        "enum" => "enum_".into(),
        "except" => "except_".into(),
        "exception" => "exception_".into(),
        "fail" => "fail_".into(),
        "false" => "false_".into(),
        "for" => "for_".into(),
        "foreign" => "foreign_".into(),
        "from" => "from_".into(),
        "if" => "if_".into(),
        "include" => "include_".into(),
        "provide" => "provide_".into(),
        "let" => "let_".into(),
        "match" => "match_".into(),
        "mut" => "mut_".into(),
        "primitive" => "primitive_".into(),
        "rec" => "rec_".into(),
        "record" => "record_".into(),
        "throw" => "throw_".into(),
        "true" => "true_".into(),
        "type" => "type_".into(),
        "void" => "void_".into(),
        "wasm" => "wasm_".into(),
        "when" => "when_".into(),
        "while" => "while_".into(),
        s => s.to_lower_camel_case(),
    }
}
