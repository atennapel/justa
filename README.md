# justa
Programming language targetting the JVM

# References
https://github.com/AndrasKovacs/elaboration-zoo

https://github.com/AndrasKovacs/staged

https://github.com/AndrasKovacs/cctt

# TODO:
## MVP:
- [x] Data types
- [x] IO
- [x] Lambda match
- [x] Operators
- [x] Modules
- [x] Public/private
- [x] Record types
- [x] Identity type
- [x] Meta datatypes
- [x] Meta-level recursion
- [x] Mutual recursive datatypes
- [x] Mutual recursion
- [x] JVM bytecode generation
- [x] JVM classes and IO access
- [ ] Datatype annotations and optimizations
- [ ] Expanded representation polymorphism
- [ ] Null handling

## Extras:
- [x] Re-exporting
- [x] Instance search
- [x] Check postponing
- [x] Computational records in elaboration
- [x] Remove unused and de-duplicate synthetic definitions
- [x] JVM array type
- [x] JVM main method helper
- [x] unsafeRunIO
- [x] Generalized variables
- [ ] JVM invoke static
- [ ] Optimize IO Unit functions
- [ ] Array creation helpers
- [ ] Primitive names should not be keyword, e.g. module name could be a primitive name such as IO
- [ ] De-duplicate generated datatypes between modules
- [ ] Generate private anonymous records if possible
- [ ] Handle recursion when de-duplicating
- [ ] Improve de-duplication and unused def removal
- [ ] Top-level recursion
- [ ] Top-level mutual recursion
- [ ] Pattern matching
- [ ] String and label types
- [ ] Import all(-hiding), re-export all(-hiding)
- [ ] Give more context for cv unification errors in elaboration
- [ ] Accept trailing and leading commas where it makes sense
- [ ] Overloaded constructors
- [ ] Meta spine eta-expansion
- [ ] Row-types records (and variants)?
- [ ] Check performance with lazy env and types
- [ ] Sugar for lists and other data structures
- [ ] Sugar for fixIx and fix
- [ ] Match on primitive types (Int, Bool)
- [ ] Fix unification issues for higher-kinded typeclasses (e.g. Functor)
- [ ] Elaborate if-expressions for meta level
