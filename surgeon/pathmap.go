/*
 * Efficient Copy-On-Write path-to-object maps
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

package main

import (
	"fmt"
	"sort"
	"strings"
)

// A PathMap represents a mapping from a set of filenames visible in a
// Subversion revision to some kind of value object.  The main use is
// by the dumpfile parser, in which the value object is a NodeAction.
//
// The reason to prefer this over a naive implementation is that
// without the copy-on-write storage sharing of snapshots, the
// cost to keep a per-revision array of snapshots can blow up
// pretty badly.
type PathMap struct {
	dirs   map[string]*PathMap
	blobs  map[string]interface{}
	shared bool
	// The following member is not used by PathMap itself, but is available to
	// users and/or wrapping structures as auxiliary storage. It is not copied
	// when snaphotting, and is thus attached to a single PathMap instance.
	info   interface{}
}

func newPathMap() *PathMap {
	pm := new(PathMap)
	pm.dirs = make(map[string]*PathMap)
	pm.blobs = make(map[string]interface{})
	pm.shared = false
	return pm
}

// _markShared sets the shared attribute on all PathMaps in the hierarchy
// When pm.shared is true, at least two Pathmaps have pm in their hierarchy,
// which means that pm should be replaced by a snapshot before any
// modification.
// It is not part of the interface, but a convenience helper
func (pm *PathMap) _markShared() {
	// We make use of the fact that pm.shared is made true only via this
	// function, and that it is never reset to false (In new snapshots it
	// will be false of course). In particular, if pm.shared is already
	// true, there is no need to recurse.
	if !pm.shared {
		pm.shared = true
		for _, v := range pm.dirs {
			v._markShared()
		}
	}
}

// snapshot returns a snapshot of the current state of an evolving filemap.
func (pm *PathMap) snapshot() *PathMap {
	// The shapshot will share its direct children with the source PathMap.
	r := new(PathMap)
	r.shared = false
	r._inplaceSnapshot(pm)
	return r
}

func (pm *PathMap) _inplaceSnapshot(source *PathMap) {
	// Mark every PathMap in the hierarchy as shared so that they are
	// considered immutable and a snapshot will be made before any
	// modification.
	dirs := make(map[string]*PathMap, len(source.dirs))
	blobs := make(map[string]interface{}, len(source.blobs))
	for k, v := range source.dirs {
		dirs[k] = v
		v._markShared()
	}
	for k, v := range source.blobs {
		blobs[k] = v
	}
	pm.dirs = dirs
	pm.blobs = blobs
}

// _unshare returns a PathMap representing the same tree as the PathMap it is
// called on, ensuring that the returned PathMap is not shared with any other
// PathMap, so that it can be modified without impacting other trees.
// When the shared attribute of the PathMap is false, _unshare returns that
// PathMap unchanged. If the shared attribute is true, _unshare returns a
// snapshot of the PathMap.
// It is not part of the interface, but a convenience helper
func (pm *PathMap) _unshare() *PathMap {
	if pm.shared {
		return pm.snapshot()
	}
	return pm
}

// _createTree ensures the hierarchy contains the directory whose path is given
// as a slice of components, creating and snapshotting PathMaps as needed.
// It is not part of the interface, but a convenience helper
func (pm *PathMap) _createTree(path []string) *PathMap {
	tree := pm
	for _, component := range path {
		subtree, ok := tree.dirs[component]
		if ok {
			// The component already exists. Unshare it so that
			// it can be modified without messing with other PathMaps
			subtree = subtree._unshare()
		} else {
			// Create the component as a directory
			subtree = newPathMap()
		}
		// Put the new or snapshot tree in place, and go down a level
		tree.dirs[component] = subtree
		tree = subtree
	}
	return tree
}

// copyFrom inserts at targetPath a copy of sourcePath in sourcePathMap.
// If targetPath is empty, then sourcePath must point to a directory in
// sourcePathMap, and the contents of pm are replaced by those of that
// directory, sharing the inner PathMaps for efficiency (pm itself cannot be
// replaced since it is a toplevel PathMap owned by calling code).
// If targetPath is empty, then sourcePath might point to a value and/or a
// directory in sourcePathMap. Both will be copied over if existing.
// The directory will be shared with sourcePathMap unless sourcePath is empty,
// in which case a snapshot of sourcePathMap is used so that sourcePathMap, a
// toplevel PathMap, is not shared.
func (pm *PathMap) copyFrom(targetPath string, sourcePathMap *PathMap, sourcePath string) {
	parts := strings.Split(sourcePath, svnSep)
	sourceDir, sourceName := parts[:len(parts)-1], parts[len(parts)-1]
	// Walk along the "dirname" in sourcePath
	sourceParent := sourcePathMap
	for _, component := range sourceDir {
		var ok bool
		if sourceParent, ok = sourceParent.dirs[component]; !ok {
			// The source path does not exist, bail out
			logit(logWARN, "nonexistent source %q on pathmap copy", component)
			return
		}
	}
	if targetPath == "" {
		var tree *PathMap
		if sourcePath == "" {
			tree = sourceParent // no need to snapshot, it will not be shared
		} else {
			var ok bool
			tree, ok = sourceParent.dirs[sourceName]
			if !ok {
				// The source path does not exist, bail out
				logit(logWARN, "missing segment %q on pathmap copy to empty target", sourceName)
				return
			}
		}
		// Same as if we were doing a new snapshot, but in place.
		pm._inplaceSnapshot(tree)
	} else {
		// Decompose targetPath into components
		parts = strings.Split(targetPath, svnSep)
		targetDir, targetName := parts[:len(parts)-1], parts[len(parts)-1]
		// And perform the copy. In normal cases, only one of the dir and file exist
		if sourcePath == "" {
			// use a snapshot instead of marking as shared, since toplevel PathMaps
			// are never expected to be shared.
			pm._createTree(targetDir).dirs[targetName] = sourceParent.snapshot()
		} else {
			if tree, ok := sourceParent.dirs[sourceName]; ok {
				tree._markShared()
				pm._createTree(targetDir).dirs[targetName] = tree
			}
			if blob, ok := sourceParent.blobs[sourceName]; ok {
				pm._createTree(targetDir).blobs[targetName] = blob
			}
		}
		// When the last component of sourcePath does not exist, we do nothing
	}
}

// get takes a path as argument, and returns the file that is stored at that
// path, if any. In that case the second return value is the boolean true.
// If there is no file in the PathMap corresponding to that path, the first
// return value is nil (the null value of the interface{} type) and the second
// return value is the boolean false
func (pm *PathMap) get(path string) (interface{}, bool) {
	// Walk along the "dirname"
	parent := pm
	for {
		i := strings.Index(path, svnSep)
		if i < 0 {
			break
		}
		component := path[:i]
		path = path[i+1:]
		var ok bool
		if parent, ok = parent.dirs[component]; !ok {
			return nil, false
		}
	}
	// Now fetch the "basename"
	element, ok := parent.blobs[path]
	return element, ok
}

// set adds a filename to the map, with associated value.
func (pm *PathMap) set(path string, value interface{}) {
	parts := strings.Split(path, svnSep)
	dir, name := parts[:len(parts)-1], parts[len(parts)-1]
	pm._createTree(dir).blobs[name] = value
}

// remove removes a filename, or all descendants of a directory name, from the map.
func (pm *PathMap) remove(path string) {
	// Separate the first component and the rest in the path
	components := strings.SplitN(path, svnSep, 2)
	component := components[0]
	if len(components) == 1 {
		// The path to delete is at pm's toplevel
		delete(pm.dirs, component)
		delete(pm.blobs, component)
	} else {
		// Try to go down a level
		subtree, ok := pm.dirs[component]
		if !ok {
			// A component in the path doesn't exist as a directory; bail out
			logit(logWARN, "component %q to be deleted is missing", component)
			return
		}
		// The component exists. Unshare it so that
		// it can be modified without messing with other PathMaps
		subtree = subtree._unshare()
		pm.dirs[component] = subtree
		// Now ask the subdir to do the removal, using the rest of the path
		subtree.remove(components[1])
		// Do not keep empty subdirectories around
		if subtree.isEmpty() {
			delete(pm.dirs, component)
		}
	}
}

// iter() calls the hook for each (path, blob) pair in the PathMap
func (pm *PathMap) iter(hook func(string, interface{})) {
	pm._iter(&[]string{}, hook)
}

func (pm *PathMap) _iter(prefix *[]string, hook func(string, interface{})) {
	pos := len(*prefix)
	*prefix = append(*prefix, "")
	for component, subdir := range pm.dirs {
		(*prefix)[pos] = component
		subdir._iter(prefix, hook)
	}
	for component, elt := range pm.blobs {
		(*prefix)[pos] = component
		hook(strings.Join(*prefix, svnSep), elt)
	}
	*prefix = (*prefix)[:pos]
}

func (pm *PathMap) size() int {
	size := len(pm.blobs)
	for _, subdir := range pm.dirs {
		size += subdir.size()
	}
	return size
}

// isEmpty returns true iff the PathMap contains no file
func (pm *PathMap) isEmpty() bool {
	return len(pm.dirs)+len(pm.blobs) == 0
}

func (pm *PathMap) clear() {
	if !pm.isEmpty() {
		*pm = *newPathMap()
	}
}

// Derived PathMap code, independent of the store implementation

func (pm *PathMap) String() string {
	var out strings.Builder
	out.WriteByte('{')
	names := pm.pathnames()
	lastIdx := len(names) - 1
	for idx, name := range names {
		value, _ := pm.get(name)
		fmt.Fprintf(&out, "%s: %v", name, value)
		if idx != lastIdx {
			out.WriteString(", ")
		}
	}
	out.WriteByte('}')
	return out.String()
}

// names returns a sorted list of the pathnames in the set
func (pm *PathMap) pathnames() []string {
	v := make([]string, pm.size())
	i := 0
	pm.iter(func(name string, _ interface{}) {
		v[i] = name
		i++
	})
	sort.Strings(v)
	return v
}

// FlatPathMap is a go map, with an interface similar to that of PathMap
type FlatPathMap map[string]interface{}

func (fpm *FlatPathMap) get(path string) (interface{}, bool) {
	a, b := (*fpm)[path]
	return a, b
}

func (fpm *FlatPathMap) set(path string, value interface{}) {
	(*fpm)[path] = value
}

func (fpm *FlatPathMap) remove(path string) {
	delete(*fpm, path)
}

func (fpm *FlatPathMap) iter(hook func(string, interface{})) {
	for path, value := range *fpm {
		hook(path, value)
	}
}

func (fpm *FlatPathMap) clear() {
	*fpm = make(FlatPathMap)
}

func (fpm *FlatPathMap) size() int {
	return len(*fpm)
}

// PathMapLike is any structure that can be modified or queried like a PathMap
// or a FlatPathMap.
type PathMapLike interface {
	get(path string) (interface{}, bool)
	set(path string, value interface{})
	remove(path string)
	clear()

	size() int
	iter(hook func(string, interface{}))
}
