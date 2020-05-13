#!/bin/sh

if [ $(uname) = "Linux" ]; then
    pathCmd="readlink -f"
elif [ $(uname) = "Darwin" ]; then
    pathCmd="stat -f %N"
else
    pathCmd="realpath"
fi

BASEDIR=`dirname $($pathCmd $0)`

# Figures out where Eldarica is installed and runs it with the proper classpath
# (partially copied from the scala dist.)
SOURCE=$0;
# Z3_LIB_PATH=/home/philipp/tmp/z3/lib
SCRIPT=`basename "${SOURCE}"`;

# Finds the root folder of the distribution, through the tempest (and the
# symbolic links)
while [ -h "${SOURCE}" ]; do
    SCRIPT=`basename "${SOURCE}"`;
    LOOKUP=`ls -ld "${SOURCE}"`;
    TARGET=`expr "${LOOKUP}" : '.*-> \(.*\)$'`;
    if expr "${TARGET:-.}/" : '/.*/$' > /dev/null; then
        SOURCE=${TARGET:-.};
    else
        SOURCE=`dirname "${SOURCE}"`/${TARGET:-.};
    fi;
done;

LAZABS_HOME=`dirname "${SOURCE}"`;

# export LD_LIBRARY_PATH=${Z3_LIB_PATH}:/usr/local/lib:/usr/local/lib/jni:/usr/lib/jni;

#if [ -z "$STAREXEC_MAX_MEM" ]; then
#	maxheap=2024
#else if [ "$STAREXEC_MAX_MEM" -gt 64000 ]; then
#	maxheap=64000
#else
#	maxheap=$((STAREXEC_MAX_MEM-5))
#fi; fi

maxheap=12000

export JAVA_OPTS="-Xmx"$maxheap"m -Xss64000k";

# binary distribution from sbt
export LAZABS_CMD="java ${JAVA_OPTS} -cp ${LAZABS_HOME}/target/scala-2.*/Eldarica-abs-assembly*.jar"

exec $LAZABS_CMD lazabs.Main "$@"
