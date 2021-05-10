# Verified NFS server

This proof is broken down into the following layers, organized top-down:

| Layer                       | Functionality                                                                                  |
| :-------------------------- | :--------------------------------------------------------------------------------------------- |
| [dir](dir_fs.dfy)           | Directories and top-level NFS API.                                                             |
| [typed](typed_fs.dfy)       | Inode allocation, and hiding invariant from all lower layers.                                  |
| [byte](byte_fs.dfy)         | Byte-based files of variable size.                                                             |
| [block](block_fs.dfy)       | Block-based files, from gathering up blocks by `Pos` per inode from indirect layer.            |
| [indirect](indirect_fs.dfy) | Indirect blocks accessed by abstract position `Pos`. Organized into a tree rooted at an inode. |
| [inode](inode_fs.dfy)       | High-level inodes with efficient in-memory access and on-disk encoding. Block allocation.      |
| [jrnl](../jrnl/jrnl.s.dfy)  | Assumed transaction-system interface.                                                          |

Some interesting libraries implementing parts of the file system include:

| Library                          | Purpose                                                                                           |
| :------------------------------- | :------------------------------------------------------------------------------------------------ |
| [nfs spec](nfs.s.dfy)            | Definitions to define the NFS specification. Also see postconditions in [dir_fs.dfy](dir_fs.dfy). |
| [mem_dirent](dir/mem_dirent.dfy) | In-memory, lazily read directories with in-place updates.                                         |
| [mem_inode](inode/mem_inode.dfy) | In-memory inodes with in-place updates.                                                           |
| [pos](indirect/pos.dfy)          | Organizes blocks in inode into a tree, determining how indirect each block is interpreted.        |
| [super](super.dfy)               | Static file-system configuration and disk layout.                                                 |
