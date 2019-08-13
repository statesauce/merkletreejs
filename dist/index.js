"use strict";
exports.__esModule = true;
var reverse = require("buffer-reverse");
var CryptoJS = require("crypto-js");
var treeify = require("treeify");
var _ = require("lodash");
function isMerkleLeaf(object) {
    return "data" in object;
}
function isMerkleNode(object) {
    return ("left" in object ||
        "right" in object ||
        "value" in object ||
        "leaf" in object ||
        "parent" in object);
}
var MerkleFromLeaves = /** @class */ (function () {
    function MerkleFromLeaves(leaves, hashAlgo, options, stopi, stopj) {
        this.i = 0;
        this.j = 0;
        this.layers = [];
        this.leaves = leaves;
        this.options = options;
        this.hashAlgo = hashAlgo;
    }
    MerkleFromLeaves.prototype.next = function () {
        this.curIsLeaf = this.layers[this.i]
            ? this.j < this.layers[this.i].length
                ? this.layers[this.i][this.j].hasOwnProperty("value")
                    ? false
                    : true
                : true
            : true;
        if (this.j % 2 === 0) {
            // left
            if (!this.curIsLeaf) {
                if (this.layers[this.i].length === 1) {
                    if (this.done) {
                        return { value: null, done: true };
                    }
                    else {
                        // root
                        var node = this.layers[this.i][this.j];
                        this.node = node;
                        this.done = true;
                        return { value: { value: node, depth: this.i }, done: false };
                    }
                }
                else if (this.j + 1 === this.layers[this.i].length &&
                    this.layers[this.i].length % 2 === 1) {
                    if (this.options.duplicateOdd) {
                        // extra left / missing right
                        this.node = this.layers[this.i][this.j];
                        this.layers[this.i].push(this.node);
                        this.j++;
                        this._createParent();
                        return {
                            value: { value: this.node, depth: this.i },
                            done: false
                        };
                    }
                    else {
                        var leaf = this.layers[this.i].pop();
                        this.node = leaf;
                        this.layers[this.i + 1].push(leaf);
                        this.j = 0;
                        this.i++;
                        return this.next();
                    }
                }
                else {
                    // normal left
                    this.node = this.layers[this.i][this.j];
                    this.j++;
                    this._createParent();
                    return { value: { value: this.node, depth: this.i }, done: false };
                }
            }
            else {
                // leaves
                if (this.i === 0
                    ? this.j + 1 === this.leaves.length && this.leaves.length % 2 === 1
                    : this.j + 1 === this.layers[this.i].length &&
                        this.layers[this.i].length % 2 === 1) {
                    // extra left / missing right leaves
                    if (this.options.duplicateOdd) {
                        // maybe iterateDuplicates option
                        var leaf = this.i === 0 ? this.leaves[this.j] : this.layers[this.i][this.j];
                        if (isMerkleLeaf(leaf)) {
                            this.node = { leaf: leaf };
                            if (this.i === 0) {
                                this.leaves.push(leaf);
                            }
                            else {
                                this.layers[this.i].push(this.node);
                            }
                        }
                        else if (isMerkleNode(leaf)) {
                            this.node = leaf;
                            this.layers[this.i].push(this.node);
                        }
                        this.layers[this.i].push(this.node);
                        this.j++;
                        this._createRightLeaf();
                        this._createParent();
                        return {
                            value: { value: this.node, depth: this.i },
                            done: false
                        };
                    }
                    else {
                        var leaf = this.i === 0 ? this.leaves[this.j] : this.layers[this.i].pop();
                        if (isMerkleLeaf(leaf)) {
                            this.node = { leaf: leaf };
                            this.layers[this.i + 1].push(this.node);
                        }
                        else if (isMerkleNode(leaf)) {
                            this.layers[this.i + 1].push(leaf);
                        }
                        this.j = 0;
                        this.i++;
                        // iteratedup here
                        return this.next();
                    }
                }
                else {
                    var leaf = this.i === 0 ? this.leaves[this.j] : this.layers[this.i][this.j];
                    if (!this.layers[this.i]) {
                        this.layers[this.i] = [];
                    }
                    if (isMerkleLeaf(leaf)) {
                        this.node = { leaf: leaf };
                        this.layers[this.i].push(this.node);
                    }
                    else if (isMerkleNode(leaf)) {
                        this.node = leaf;
                    }
                    this.j++;
                    this._createRightLeaf();
                    this._createParent();
                    return { value: { value: this.node, depth: this.i }, done: false };
                }
            }
        }
        else {
            this._moveRight();
            return { value: { value: this.node, depth: this.i }, done: false };
        }
    };
    MerkleFromLeaves.prototype._createRightLeaf = function () {
        var leaf = this.i === 0 ? this.leaves[this.j] : this.layers[this.i][this.j];
        if (isMerkleLeaf(leaf)) {
            var node = { leaf: leaf };
            this.layers[this.i].push(node);
        }
        else if (isMerkleNode(leaf)) {
            var node = leaf;
        }
    };
    MerkleFromLeaves.prototype._moveRight = function () {
        this.node = this.layers[this.i][this.j];
        this.curIsLeaf = this.layers[this.i]
            ? this.j < this.layers[this.i].length
                ? this.layers[this.i][this.j].hasOwnProperty("value")
                    ? false
                    : true
                : true
            : true;
        if (!this.curIsLeaf) {
            if (this.i === 0
                ? this.j === this.leaves.length - 1
                : this.j === this.layers[this.i].length - 1) {
                // end of layer
                this.j = 0;
                this.i++;
            }
            else {
                this.j++;
            }
        }
        else {
            if (this.i === 0
                ? this.j == this.leaves.length - 1
                : this.j === this.layers[this.i].length - 1) {
                this.j = 0;
                this.i++;
            }
            else {
                this.j++;
            }
        }
    };
    MerkleFromLeaves.prototype._createParent = function () {
        var parent = {
            left: this.layers[this.i][this.j - 1],
            right: this.layers[this.i][this.j]
        }; //this.layers[this.i + 1][this.layers[this.i + 1].length - 1];
        if (this.layers.length === this.i + 1) {
            this.layers.push([]);
        }
        this.layers[this.i + 1].push(parent);
        var combined = [];
        combined.push(parent.left.value ? parent.left.value : parent.left.leaf.data, parent.right.value ? parent.right.value : parent.right.leaf.data);
        if (this.options.sortPairs) {
            combined.sort(Buffer.compare);
        }
        var data = Buffer.concat(combined);
        var hash = this.hashAlgo(data);
        parent.value = hash;
        parent.left.parent = parent;
        parent.right.parent = parent;
    };
    MerkleFromLeaves.prototype[Symbol.iterator] = function () {
        return this;
    };
    return MerkleFromLeaves;
}());
exports.MerkleFromLeaves = MerkleFromLeaves;
var MerkleTree = /** @class */ (function () {
    /**
     * @desc Constructs a Merkle Tree.
     * All nodes and leaves are stored as Buffers.
     * Lonely leaf nodes are promoted to the next level up without being hashed again.
     * @param {Buffer[]} leaves - Array of hashed leaves. Each leaf must be a Buffer.
     * @param {Function} hashAlgorithm - Algorithm used for hashing leaves and nodes
     * @param {Object} options - Additional options
     * @example
     *```js
     *const MerkleTree = require('merkletreejs')
     *const crypto = require('crypto')
     *
     *function sha256(data) {
     *  // returns Buffer
     *  return crypto.createHash('sha256').update(data).digest()
     *}
     *
     *const leaves = ['a', 'b', 'c'].map(x => keccak(x))
     *
     *const tree = new MerkleTree(leaves, sha256)
     *```
     */
    function MerkleTree(leaves, hashAlgorithm, options) {
        if (options === void 0) { options = {}; }
        this.isBitcoinTree = !!options.isBitcoinTree;
        this.hashLeaves = !!options.hashLeaves;
        this.sortLeaves = !!options.sortLeaves;
        this.sortPairs = !!options.sortPairs;
        this.sort = !!options.sort;
        if (this.sort) {
            this.sortLeaves = true;
            this.sortPairs = true;
        }
        this.duplicateOdd = !!options.duplicateOdd;
        this.hashAlgo = bufferifyFn(hashAlgorithm);
        if (this.hashLeaves) {
            leaves = leaves.map(this.hashAlgo);
        }
        this.leaves = leaves.map(bufferify);
        if (this.sortLeaves) {
            this.leaves = this.leaves.sort(Buffer.compare);
        }
        this.layers = [this.leaves];
        this.createHashes(this.leaves);
    }
    // TODO: documentation
    MerkleTree.prototype.createHashes = function (nodes) {
        while (nodes.length > 1) {
            var layerIndex = this.layers.length;
            this.layers.push([]);
            for (var i = 0; i < nodes.length; i += 2) {
                if (i + 1 === nodes.length) {
                    if (nodes.length % 2 === 1) {
                        var data_1 = nodes[nodes.length - 1];
                        var hash_1 = data_1;
                        // is bitcoin tree
                        if (this.isBitcoinTree) {
                            // Bitcoin method of duplicating the odd ending nodes
                            data_1 = Buffer.concat([reverse(data_1), reverse(data_1)]);
                            hash_1 = this.hashAlgo(data_1);
                            hash_1 = reverse(this.hashAlgo(hash_1));
                            this.layers[layerIndex].push(hash_1);
                            continue;
                        }
                        else {
                            if (!this.duplicateOdd) {
                                this.layers[layerIndex].push(nodes[i]);
                                continue;
                            }
                        }
                    }
                }
                var left = nodes[i];
                var right = i + 1 == nodes.length ? left : nodes[i + 1];
                var data = null;
                var combined = null;
                if (this.isBitcoinTree) {
                    combined = [reverse(left), reverse(right)];
                }
                else {
                    combined = [left, right];
                }
                if (this.sortPairs) {
                    combined.sort(Buffer.compare);
                }
                data = Buffer.concat(combined);
                var hash = this.hashAlgo(data);
                // double hash if bitcoin tree
                if (this.isBitcoinTree) {
                    hash = reverse(this.hashAlgo(hash));
                }
                this.layers[layerIndex].push(hash);
            }
            nodes = this.layers[layerIndex];
        }
    };
    /**
     * getLeaves
     * @desc Returns array of leaves of Merkle Tree.
     * @return {Buffer[]}
     * @example
     *```js
     *const leaves = tree.getLeaves()
     *```
     */
    MerkleTree.prototype.getLeaves = function () {
        return this.leaves;
    };
    /**
     * getLayers
     * @desc Returns array of all layers of Merkle Tree, including leaves and root.
     * @return {Buffer[]}
     * @example
     *```js
     *const layers = tree.getLayers()
     *```
     */
    MerkleTree.prototype.getLayers = function () {
        return this.layers;
    };
    /**
     * getRoot
     * @desc Returns the Merkle root hash as a Buffer.
     * @return {Buffer}
     * @example
     *```js
     *const root = tree.getRoot()
     *```
     */
    MerkleTree.prototype.getRoot = function () {
        return this.layers[this.layers.length - 1][0] || Buffer.from([]);
    };
    // TODO: documentation
    MerkleTree.prototype.getHexRoot = function () {
        return bufferToHex(this.getRoot());
    };
    /**
     * getProof
     * @desc Returns the proof for a target leaf.
     * @param {Buffer} leaf - Target leaf
     * @param {Number} [index] - Target leaf index in leaves array.
     * Use if there are leaves containing duplicate data in order to distinguish it.
     * @return {Object[]} - Array of objects containing a position property of type string
     * with values of 'left' or 'right' and a data property of type Buffer.
     *@example
     * ```js
     *const proof = tree.getProof(leaves[2])
     *```
     *
     * @example
     *```js
     *const leaves = ['a', 'b', 'a'].map(x => keccak(x))
     *const tree = new MerkleTree(leaves, keccak)
     *const proof = tree.getProof(leaves[2], 2)
     *```
     */
    MerkleTree.prototype.getProof = function (leaf, index) {
        leaf = bufferify(leaf);
        var proof = [];
        if (typeof index !== "number") {
            index = -1;
            for (var i = 0; i < this.leaves.length; i++) {
                if (Buffer.compare(leaf, this.leaves[i]) === 0) {
                    index = i;
                }
            }
        }
        if (index <= -1) {
            return [];
        }
        if (this.isBitcoinTree && index === this.leaves.length - 1) {
            // Proof Generation for Bitcoin Trees
            for (var i = 0; i < this.layers.length - 1; i++) {
                var layer = this.layers[i];
                var isRightNode = index % 2;
                var pairIndex = isRightNode ? index - 1 : index;
                var position = isRightNode ? "left" : "right";
                if (pairIndex < layer.length) {
                    proof.push({
                        data: layer[pairIndex]
                    });
                }
                // set index to parent index
                index = (index / 2) | 0;
            }
            return proof;
        }
        else {
            // Proof Generation for Non-Bitcoin Trees
            for (var i = 0; i < this.layers.length; i++) {
                var layer = this.layers[i];
                var isRightNode = index % 2;
                var pairIndex = isRightNode ? index - 1 : index + 1;
                if (pairIndex < layer.length) {
                    proof.push({
                        position: isRightNode ? "left" : "right",
                        data: layer[pairIndex]
                    });
                }
                // set index to parent index
                index = (index / 2) | 0;
            }
            return proof;
        }
    };
    // TODO: documentation
    MerkleTree.prototype.getHexProof = function (leaf, index) {
        return this.getProof(leaf, index).map(function (x) { return bufferToHex(x.data); });
    };
    /**
     * verify
     * @desc Returns true if the proof path (array of hashes) can connect the target node
     * to the Merkle root.
     * @param {Object[]} proof - Array of proof objects that should connect
     * target node to Merkle root.
     * @param {Buffer} targetNode - Target node Buffer
     * @param {Buffer} root - Merkle root Buffer
     * @return {Boolean}
     * @example
     *```js
     *const root = tree.getRoot()
     *const proof = tree.getProof(leaves[2])
     *const verified = tree.verify(proof, leaves[2], root)
     *```
     */
    MerkleTree.prototype.verify = function (proof, targetNode, root) {
        var hash = bufferify(targetNode);
        root = bufferify(root);
        if (!Array.isArray(proof) || !proof.length || !targetNode || !root) {
            return false;
        }
        for (var i = 0; i < proof.length; i++) {
            var node = proof[i];
            var data = null;
            var isLeftNode = null;
            // NOTE: case for when proof is hex values only
            if (typeof node === "string") {
                data = bufferify(node);
                isLeftNode = true;
            }
            else {
                data = node.data;
                isLeftNode = node.position === "left";
            }
            var buffers = [];
            if (this.isBitcoinTree) {
                buffers.push(reverse(hash));
                buffers[isLeftNode ? "unshift" : "push"](reverse(data));
                hash = this.hashAlgo(Buffer.concat(buffers));
                hash = reverse(this.hashAlgo(hash));
            }
            else {
                if (this.sortPairs) {
                    if (Buffer.compare(hash, data) === -1) {
                        buffers.push(hash, data);
                        hash = this.hashAlgo(Buffer.concat(buffers));
                    }
                    else {
                        buffers.push(data, hash);
                        hash = this.hashAlgo(Buffer.concat(buffers));
                    }
                }
                else {
                    buffers.push(hash);
                    buffers[isLeftNode ? "unshift" : "push"](data);
                    hash = this.hashAlgo(Buffer.concat(buffers));
                }
            }
        }
        return Buffer.compare(hash, root) === 0;
    };
    // TODO: documentation
    MerkleTree.prototype.getLayersAsObject = function () {
        var _a;
        var layers = this.getLayers().map(function (x) { return x.map(function (x) { return x.toString("hex"); }); });
        var objs = [];
        for (var i = 0; i < layers.length; i++) {
            var arr = [];
            for (var j = 0; j < layers[i].length; j++) {
                var obj = (_a = {}, _a[layers[i][j]] = null, _a);
                if (objs.length) {
                    obj[layers[i][j]] = {};
                    var a = objs.shift();
                    var akey = Object.keys(a)[0];
                    obj[layers[i][j]][akey] = a[akey];
                    if (objs.length) {
                        var b = objs.shift();
                        var bkey = Object.keys(b)[0];
                        obj[layers[i][j]][bkey] = b[bkey];
                    }
                }
                arr.push(obj);
            }
            objs.push.apply(objs, arr);
        }
        return objs[0];
    };
    // TODO: documentation
    MerkleTree.prototype.print = function () {
        MerkleTree.print(this);
    };
    // TODO: documentation
    MerkleTree.prototype.toTreeString = function () {
        var obj = this.getLayersAsObject();
        return treeify.asTree(obj, true);
    };
    // TODO: documentation
    MerkleTree.prototype.toString = function () {
        return this.toTreeString();
    };
    // TODO: documentation
    MerkleTree.bufferify = function (x) {
        return bufferify(x);
    };
    // TODO: documentation
    MerkleTree.print = function (tree) {
        console.log(tree.toString());
    };
    return MerkleTree;
}());
function bufferToHex(value) {
    return "0x" + value.toString("hex");
}
function bufferify(x) {
    if (!Buffer.isBuffer(x)) {
        // crypto-js support
        if (typeof x === "object" && x.words) {
            return Buffer.from(x.toString(CryptoJS.enc.Hex), "hex");
        }
        else if (isHexStr(x)) {
            return Buffer.from(x.replace(/^0x/, ""), "hex");
        }
        else if (typeof x === "string") {
            return Buffer.from(x);
        }
    }
    return x;
}
function bufferifyFn(f) {
    return function (x) {
        var v = f(x);
        if (Buffer.isBuffer(v)) {
            return v;
        }
        if (isHexStr(v)) {
            return Buffer.from(v, "hex");
        }
        // crypto-js support
        return Buffer.from(f(CryptoJS.enc.Hex.parse(x.toString("hex"))).toString(CryptoJS.enc.Hex), "hex");
    };
}
function isHexStr(v) {
    return typeof v === "string" && /^(0x)?[0-9A-Fa-f]*$/.test(v);
}
exports["default"] = { MerkleTree: MerkleTree, MerkleFromLeaves: MerkleFromLeaves };
