vopt -L DW work.Sit_mod -o Sit_mod_opt +cover
vsim -L DW -coverage work.Sit_mod_opt +notimingchecks

