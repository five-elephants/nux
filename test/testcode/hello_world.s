# Copyright 2015 Heidelberg University Copyright and related rights are
# licensed under the Solderpad Hardware License, Version 0.51 (the "License");
# you may not use this file except in compliance with the License. You may obtain
# a copy of the License at http://solderpad.org/licenses/SHL-0.51. Unless
# required by applicable law or agreed to in writing, software, hardware and
# materials distributed under this License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See
# the License for the specific language governing permissions and limitations
# under the License.


	.file	"hello_world.c"
	.gnu_attribute 4, 1
	.gnu_attribute 8, 1
	.gnu_attribute 12, 1
	.section	".text"
	.align 2
	.globl mem_set
	.type	mem_set, @function
mem_set:
	cmpwi 7,4,0
	addi 3,3,-4
	addi 0,4,1
	bge+ 7,.L2
	li 0,1
	b .L2
.L3:
	stwu 5,4(3)
.L2:
	addic. 0,0,-1
	bne+ 0,.L3
	blr
	.size	mem_set, .-mem_set
	.align 2
	.globl vector_add
	.type	vector_add, @function
vector_add:
	cmpwi 7,6,0
	li 9,0
	addi 0,6,1
	bge+ 7,.L6
	li 0,1
	b .L6
.L7:
	lwzx 10,5,9
	lwzx 11,4,9
	add 11,10,11
	stwx 11,3,9
	addi 9,9,4
.L6:
	addic. 0,0,-1
	bne+ 0,.L7
	blr
	.size	vector_add, .-vector_add
	.align 2
	.globl hello_world
	.type	hello_world, @function
hello_world:
	mflr 0
	stwu 1,-8(1)
	li 11,4
	li 9,0
	li 10,12
	li 3,40
	stw 0,12(1)
	li 0,1
	stw 9,0(9)
	li 9,8
	stw 0,0(11)
	li 0,2
	stw 0,0(9)
	li 0,3
	stw 0,0(10)
	li 10,16
	stw 11,0(10)
	li 0,5
	li 11,20
	li 4,10
	stw 0,0(11)
	li 0,6
	li 11,24
	li 5,1
	stw 0,0(11)
	li 0,7
	li 11,28
	stw 0,0(11)
	li 11,32
	stw 9,0(11)
	li 0,9
	li 9,36
	stw 0,0(9)
	bl mem_set
	lwz 0,12(1)
	li 3,80
	li 4,0
	mtlr 0
	li 5,40
	li 6,10
	addi 1,1,8
	b vector_add
	.size	hello_world, .-hello_world
	.ident	"GCC: (GNU) 4.5.0"
