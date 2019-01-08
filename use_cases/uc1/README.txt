In order to check the LTL SPEC follow these steps:

-open a terminal and run NuSMV  typing the command:

 NuSMV -int

-in NuSMV prompt type:

 read_model -i SystemComposition.smv
 flatten_hierarchy
 encode_variables
 build_model
 check_ltlspec



LTL SPEC are defined in main MODULE. There are three property to check:

-always in the future mission=succeeded
-always is_bottle_found = succeeded precedes req_Fetch_bottle
-always (GO_TO_KITCHEN_inst.to_bt=succeeded & FIND_BOTTLE_inst.to_bt=succeeded & FETCH_BOTTLE_inst.to_bt=succeeded) precedes mission=succeeded or
 always ASK_FOR_HELP_inst.to_bt=succeeded precedes mission=succeeded
