if [ $# -lt 1 ]
then
    echo "I need a release tag"
    exit 1
fi

if [ $1 == "" ]
then
    echo "release tag should not be empty"
    exit 1
fi

GIT_COMMITTER_DATE=$(git log -n1 --pretty=%aD) git tag -a -m "Release $1" "$1"
git push --tags
