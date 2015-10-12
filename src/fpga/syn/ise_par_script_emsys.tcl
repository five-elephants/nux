#########################
###  DEFINE VARIABLES ###
#########################
set DesignName	"emsys_top"
set FamilyName	"VIRTEX5"
set DeviceName	"XC5VLX110T"
set PackageName	"FF1136"
set SpeedGrade	"-1"
set TopModule	"Emsys_top"
set EdifFile	"emsys_top.edf"


if { [file exists $DesignName.xise]} {
	file delete $DesignName.xise
	file delete -force $DesignName.gise
}

#if {![file exists $DesignName.xise]} {

project new $DesignName.xise

project set family $FamilyName
project set device $DeviceName
project set package $PackageName
project set speed $SpeedGrade

xfile add $EdifFile
if {[file exists synplicity.ucf]} {
    xfile add synplicity.ucf
}

project set "Netlist Translation Type" "Timestamp"
#project set "Other NGDBuild Command Line Options" "-verbose -bm /fastnbig/home/sfriedma/s2pp/fpga/memory.bmm"
project set "Other NGDBuild Command Line Options" "-verbose"
project set "Generate Detailed MAP Report" TRUE

project close
#}


file delete -force $DesignName\_xdb

project open $DesignName.xise

process run "Implement Design" -force rerun_all

project close
