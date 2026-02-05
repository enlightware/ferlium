// Copyright 2026 Enlightware GmbH
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License. You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
//
// src/lib.rs
use proc_macro::TokenStream;
use quote::quote;

use crate::ptr::FERLIUM_PTR_SIZE;

mod native_fn_aliases;
mod ptr;

#[proc_macro]
pub fn declare_native_fn_aliases(input: TokenStream) -> TokenStream {
    use native_fn_aliases::*;
    use syn::*;

    let n = parse_macro_input!(input as LitInt);
    let arity = n.base10_parse::<usize>().unwrap();

    let arg_codes = ["N", "M", "V", "W"];
    let output_codes = ["N", "V", "FN", "FV"];

    let mut generated = quote! {};

    let arg_combinations = generate_combinations(&arg_codes, arity);

    for arg_combo in arg_combinations {
        for output_code in &output_codes {
            let alias_name = generate_alias_name(arity, &arg_combo, output_code);
            let (fn_type, need_lifetime) = generate_fn_type(arity, &arg_combo, output_code);

            let generic_params = generate_generic_params(&arg_combo, output_code);
            let alias = if need_lifetime {
                quote! {
                    pub type #alias_name<'a, #(#generic_params),*> = #fn_type;
                }
            } else {
                quote! {
                    pub type #alias_name<#(#generic_params),*> = #fn_type;
                }
            };

            generated.extend(alias);
        }
    }

    generated.into()
}

/// Attribute macro for Ferlium FFI record layout.
/// Usage:
/// #[ferlium_record]
/// pub struct MyRecord {
///     a: i8,
///     b: i64,
///     c: i32,
/// }
///
/// This will emit:
/// #[repr(C)]
/// pub struct MyRecord {
///     b: i64, // align 8
///     c: i32, // align 4
///     a: i8,  // align 1
/// }
#[proc_macro_attribute]
pub fn ferlium_record(_attr: TokenStream, item: TokenStream) -> TokenStream {
    use syn::*;

    let mut input = parse_macro_input!(item as ItemStruct);

    let fields = match &mut input.fields {
        Fields::Named(named) => &mut named.named,
        _ => {
            return syn::Error::new_spanned(
                &input,
                "#[ferlium_record] only supports structs with named fields",
            )
            .to_compile_error()
            .into();
        }
    };

    // Extract fields into a vector we can sort.
    let mut field_infos: Vec<(usize, Ident, Type, Field)> = fields
        .iter()
        .enumerate()
        .map(|(idx, f)| {
            let ident = f.ident.clone().expect("named field");
            let ty = f.ty.clone();
            (idx, ident, ty, f.clone())
        })
        .collect();

    let field_size = |ty: &Type| {
        if let Type::Path(tp) = ty {
            if let Some(ident) = tp.path.segments.last().map(|s| &s.ident) {
                match ident.to_string().as_str() {
                    "i64" | "u64" | "f64" => return 8,
                    "i32" | "u32" | "f32" => return 4,
                    "i16" | "u16" => return 2,
                    "i8" | "u8" | "bool" => return 1,
                    "isize" | "usize" => return FERLIUM_PTR_SIZE,
                    _ => {}
                }
            }
        }
        // Pointers or unknown types: assume 4
        FERLIUM_PTR_SIZE
    };

    // Sort by decreasing alignment score, then by field name.
    field_infos.sort_by(|(_, name_a, ty_a, _), (_, name_b, ty_b, _)| {
        let aa = field_size(ty_a);
        let ab = field_size(ty_b);

        aa.cmp(&ab)
            .reverse()
            .then_with(|| name_a.to_string().cmp(&name_b.to_string()))
    });

    // Replace fields with sorted copies.
    fields.clear();
    for (_, _, _, field) in field_infos {
        fields.push(field);
    }

    // Add #[repr(C)] if not already present.
    let mut attrs = input.attrs.clone();
    let has_repr_c = attrs.iter().any(|attr| attr.path().is_ident("repr"));

    if !has_repr_c {
        let repr_attr: syn::Attribute = syn::parse_quote!(#[repr(C)]);
        attrs.push(repr_attr);
        input.attrs = attrs;
    }

    TokenStream::from(quote! { #input })
}
