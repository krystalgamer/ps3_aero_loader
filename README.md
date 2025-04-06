# PS3 Loader for IDA 9.1

Ported [aerosoul's loader](https://github.com/aerosoul94/ida_gel/tree/master/src) to modern IDA. Most of the work was on migrating the SDK. Also upgraded to tinyxml2.


You must build this with `__EA64__`.

## Notes

Removed the marking imports as library functions because it was crashing IDA. `add_func` went too strong.
