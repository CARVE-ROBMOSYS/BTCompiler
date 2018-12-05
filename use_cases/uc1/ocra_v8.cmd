set on_failure_script_quits;
set ocra_discrete_time;
ocra_check_consistency -i ./uc1-env_v8.oss;
reset;
ocra_check_refinement -i ./uc1-env_v8.oss;
reset;
ocra_check_implementation -i ./uc1-env_v8.oss -I ./uc1-env_v8.smv -c BT_FSM;
quit;
