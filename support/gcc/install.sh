#!/bin/bash

WORK_DIR=`pwd`/s2pp-gcc-work
DOWNLOAD_DIR=$WORK_DIR/downloads
PREFIX=`pwd`/install


TARGET=powerpc-linux-eabi

BINUTILS_URL=http://ftp.gnu.org/gnu/binutils/binutils-2.25.tar.bz2
GCC_URL=ftp://ftp.fu-berlin.de/unix/languages/gcc/releases/gcc-4.9.2/gcc-4.9.2.tar.bz2
#GMP_URL=ftp://ftp.gmplib.org/pub/gmp-4.3.2/gmp-4.3.2.tar.bz2
GMP_URL=ftp://ftp.gmplib.org/pub/gmp-5.0.2/gmp-5.0.2.tar.bz2
#MPFR_URL=http://www.mpfr.org/mpfr-current/mpfr-3.0.1.tar.bz2
MPFR_URL=http://www.mpfr.org/mpfr-current/mpfr-3.1.2.tar.bz2
#MPC_URL=http://www.multiprecision.org/mpc/download/mpc-0.8.2.tar.gz
MPC_URL=http://www.multiprecision.org/mpc/download/mpc-0.9.tar.gz
PPL_URL=ftp://ftp.cs.unipr.it/pub/ppl/releases/0.11.2/ppl-0.11.2.tar.bz2
CLOOG_URL=http://gcc.gnu.org/pub/gcc/infrastructure/cloog-ppl-0.15.11.tar.gz
ISL_URL=ftp://gcc.gnu.org/pub/gcc/infrastructure/isl-0.14.tar.bz2


#DOWNLOADS="$BINUTILS_URL $GCC_URL $GMP_URL $MPFR_URL $MPC_URL $PPL_URL $ISL_URL"
DOWNLOADS="$BINUTILS_URL $GCC_URL"

## ## download ###
echo "*** downloading source code archives ***"
mkdir -p $DOWNLOAD_DIR
pushd .
cd $DOWNLOAD_DIR

for file in $DOWNLOADS ; do
	DEST=`basename $file`
	if [ ! -f $DEST ] ; then
		#curl --proxy "" -C - -O $file
		curl -C - -O $file
	fi
done

popd

### extract ###
echo "*** extracting source code archives ***"
pushd .
cd $WORK_DIR

for file in $DOWNLOADS ; do
  tar axf downloads/`basename $file` --skip-old-files
done

popd


### compile ###
echo "*** compiling source code ***"

export CC="gcc"
export CXX="g++"
export LD_LIBRARY_PATH=$PREFIX/lib:$PREFIX/lib64:$LD_LIBRARY_PATH
export CPPFLAGS=-I$PREFIX/include
pushd .

echo "Patching binutils-2.25"
cd $WORK_DIR
patch -p0 <../binutils/binutils-2.25.patch
cd ..

echo "Building binutils-2.25"
cd $WORK_DIR/binutils-2.25
./configure --prefix=$PREFIX --target=$TARGET && make || exit
make install || exit

echo "Building gcc-4.9.2"
mkdir $WORK_DIR/gcc-build
cd $WORK_DIR/gcc-build
../gcc-4.9.2/configure --prefix=$PREFIX --target=$TARGET --disable-shared --with-gnu-as --with-as=$PREFIX/bin/powerpc-linux-eabi-as --disable-multilib --disable-threads --disable-tls --enable-target-optspace --enable-languages=c --disable-libssp --disable-libquadmath --disable-libgomp --disable-lto && make -j2 || exit
make install || exit

popd

echo "*** Installation complete ***"
