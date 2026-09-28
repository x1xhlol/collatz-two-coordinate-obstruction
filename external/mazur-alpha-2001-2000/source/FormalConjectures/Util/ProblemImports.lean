/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Logic.Function.Iterate

/-!
# Minimal Formal Conjectures problem imports

This local shim preserves the small part of `FormalConjectures.Util.ProblemImports`
needed by the Erdős 1135 target while allowing this project to track a newer mathlib
than the upstream Formal Conjectures package currently uses.
-/

namespace FormalConjectures

syntax problemStatus := &"open" <|> &"solved"
syntax CategorySyntax := &"textbook" <|> (&"research" problemStatus) <|> &"test" <|> &"API"
syntax (name := Category_attr) "category" CategorySyntax : attr

initialize Lean.registerBuiltinAttribute {
  name := `Category_attr
  descr := "Compatibility annotation for the Formal Conjectures problem category."
  add := fun _decl _stx _attrKind => pure ()
}

syntax subjectList := many(num)
syntax (name := problemSubject) "AMS" subjectList : attr

initialize Lean.registerBuiltinAttribute {
  name := `problemSubject
  descr := "Compatibility annotation for AMS subject tags."
  add := fun _decl _stx _attrKind => pure ()
}

end FormalConjectures
