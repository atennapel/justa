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
- [ ] Remove unused and de-duplicate synthetic definitions
- [ ] JVM bytecode generation
- [ ] Datatype annotations and optimizations
- [ ] Expanded representation polymorphism
- [ ] Null handling
- [ ] Generate private anonymous records if possible

## Extras:
- [x] Re-exporting
- [x] Instance search
- [x] Check postponing
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
