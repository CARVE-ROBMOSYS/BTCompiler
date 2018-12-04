# How to run the test?

In order to regenerate the OCRA `.oss` and NuSMV `.smv` files from the BT specification
`.xml`:

```
../readskill.native ./skills.xml
../mkspec.native ./system.xml
```

Then to run the OCRA analyses:

```
ocra-linux64 -source ./ocra.cmd
```

Also refer to:

```
nuXmv ./edited_system.smv
```

which represent the SMV encoding of the contracts.


