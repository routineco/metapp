# metapp: meta-preprocessor for OCaml

`metapp` is a PPX rewriter that provides a `[%meta ...]` extension,
where the dots `...` are arbitrary OCaml expressions that are
substituted at compile-time by the AST nodes they evaluate to.
These expressions build AST nodes either by quoting some code directly,
or by using `compiler-libs` ([`Parsetree`], [`Ast_helper`], ...).

[`Parsetree`]: https://caml.inria.fr/pub/docs/manual-ocaml/compilerlibref/Parsetree.html
[`Ast_helper`]: https://caml.inria.fr/pub/docs/manual-ocaml/compilerlibref/Ast_helper.html

In particular, this preprocessor is easy to use for conditional
compilation, and is an alternative to [`cppo`] and [`ppx_optcomp`].

[`cppo`]: https://github.com/ocaml-community/cppo
[`ppx_optcomp`]: https://github.com/janestreet/ppx_optcomp

```ocaml
let option_get o =
  [%meta if Sys.ocaml_version >= "4.08.0" then
     [%e Option.get o]
  else
     [%e match o with
     | None -> invalid_arg "option_get"
     | Some x -> x]]
```

Inside `[%meta ...]` code, the `[%e ...]` extension quotes expressions
(of type [`Parsetree.expression`]). There are other quotations
available: the full list is given below.

|Quotation                    |Type                      |
|-----------------------------|--------------------------|
|`[%e ...]` or `[%expr ...]`  |`Parsetree.expression`    |
|`[%p? ...]` or `[%pat? ...]` |`Parsetree.pattern`       |
|`[%t: ...]` or `[%type: ...]`|`Parsetree.core_type`     |
|`[%sig: ...]`                |`Parsetree.signature`     |
|`[%sigi: ...]`               |`Parsetree.signature_item`|
|`[%str ...]`                 |`Parsetree.structure`     |
|`[%stri ...]`                |`Parsetree.structure_item`|

Quoted expressions can in turn contain further `[%meta ...]` code.

In addition to this syntax extension, the `Metapp_utils` module
provided by the `metapp.utils` package provides convenient functions
for AST constructions.  In particular, this module provides an
OCaml-version-independent interface.  Moveover, this module provides a
common signature `ValueS` for constructing and transforming
expressions (module `Exp`), patterns (module `Pat`) or both at the
same time (module `Value`).

Global definitions for meta-code can be included with `[%%metadef
...]`.  By default, the meta-code is compiled with `compiler-libs` and
the `metapp.utils` package.
Other packages can be loaded with `[%%metapackage ...]`.
More generally, flags can be passed to the compiler to compile meta-code
with `[%%metaflags ...]` (there is another convenient notation for
adding interface directories: `[%%metadirectory ...]`).
`[%%metaload ...]` loads a particular compilation unit.
