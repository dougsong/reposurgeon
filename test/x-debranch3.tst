## Test path modification of debranch
#
# Here's the topology of debranch3.fi:
#
#         :2
#         |
#         :4
#         |
#         :6
#         |
#         +-----------+
#         |           |
#         :9          :15
#         |           |
#         :11         :17
#         |           |
#         :13      [master]
#         |
#     [alternate]
#
read <debranch3.fi
debranch alternate master
write -
echo 1
:17 paths
:15 paths
:13 paths
:11 paths
:9 paths
:6 paths
:4 paths
:2 paths
:9 inspect
:15 inspect
:6 inspect
