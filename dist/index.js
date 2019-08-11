"use strict";
var __assign = (this && this.__assign) || function () {
    __assign = Object.assign || function(t) {
        for (var s, i = 1, n = arguments.length; i < n; i++) {
            s = arguments[i];
            for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p))
                t[p] = s[p];
        }
        return t;
    };
    return __assign.apply(this, arguments);
};
Object.defineProperty(exports, "__esModule", { value: true });
var reverse = require("buffer-reverse");
var CryptoJS = require("crypto-js");
var treeify = require("treeify");
var _ = require("lodash");
/**
 * Class reprensenting a Merkle Tree
 * @namespace MerkleTree
 */
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
    function MerkleTree(_a) {
        var _this = this;
        var create = _a.create, recreate = _a.recreate;
        if (!!create) {
            if (!create.options) {
                create.options = {};
            }
            this.isBitcoinTree = !!create.options.isBitcoinTree;
            this.hashLeaves = !!create.options.hashLeaves;
            this.sortLeaves = !!create.options.sortLeaves;
            this.sortPairs = !!create.options.sortPairs;
            this.createLeaves = this.isBitcoinTree
                ? false
                : create.options.createLeaves;
            this.sort = !!create.options.sort;
            if (this.sort) {
                this.sortLeaves = true;
                this.sortPairs = true;
            }
            this.duplicateOdd = !!create.options.duplicateOdd;
            this.hashAlgo = bufferifyFn(create.hashAlgorithm);
            if (this.hashLeaves) {
                create.leaves = create.leaves.map(this.hashAlgo);
            }
            if (this.createLeaves) {
                create.leaves = create.leaves.map(this.createLeaves);
            }
            this.leaves = create.leaves.map(this.bufferify());
            if (this.sortLeaves) {
                this.leaves = this.leaves.sort(function (x, y) {
                    return _this.createLeaves
                        ? Buffer.compare(x.value, y.value)
                        : Buffer.compare(x, y);
                });
            }
            this.layers = [this.leaves];
            this.createHashes(this.leaves);
        }
        else if (!!recreate) {
            if (!recreate.options) {
                recreate.options = {};
            }
            this.leaves = recreate.leaves;
            this.layers = recreate.layers;
        }
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
                    combined = this.createLeaves
                        ? [
                            Buffer.isBuffer(left) ? left : left.value,
                            Buffer.isBuffer(right) ? right : right.value
                        ]
                        : [left, right];
                }
                if (this.sortPairs) {
                    // this.createLeaves && layerIndex === 1
                    //   ? combined.sort((x, y) => Buffer.compare(x.value, y.value))
                    //   :
                    combined.sort(Buffer.compare);
                }
                data = Buffer.concat(combined);
                // this.createLeaves && layerIndex == 1
                //   ? Buffer.concat(combined.map(x => x.value))
                //   :
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
                if (Buffer.compare(leaf, this.leaves[i].value) === 0) {
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
                        data: this.createLeaves && i === 0
                            ? layer[pairIndex].value
                            : layer[pairIndex]
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
    MerkleTree.prototype.getLayersAsObject = function () {
        var _layers = _.cloneDeep(this.getLayers());
        var layers = [
            _layers.shift().map(function (x) {
                return __assign({}, x, { value: "0x" + x.value.toString("hex") });
            })
        ];
        layers.push.apply(layers, _layers.map(function (x) { return x.map(function (x) { return "0x" + x.toString("hex"); }); }));
        var objs = [];
        for (var i = 0; i < layers.length; i++) {
            var arr = [];
            for (var j = 0; j < layers[i].length; j++) {
                var el = layers[i][j];
                var obj = {};
                if (i === 0 && this.createLeaves) {
                    obj[el.value] = el;
                    delete obj[el.value].value;
                }
                else {
                    obj[el] = null;
                }
                if (objs.length) {
                    obj[el] = {};
                    var a = objs.shift();
                    var akey = Object.keys(a)[0];
                    obj[el][akey] = a[akey];
                    if (objs.length) {
                        var b = objs.shift();
                        var bkey = Object.keys(b)[0];
                        obj[el][bkey] = b[bkey];
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
    MerkleTree.prototype.bufferify = function () {
        if (this.createLeaves) {
            return function (x) {
                return __assign({}, x, { value: bufferify(x.value) });
            };
        }
        else {
            return function (x) {
                return bufferify(x);
            };
        }
    };
    // TODO: documentation
    MerkleTree.print = function (tree) {
        console.log(tree.toString());
    };
    return MerkleTree;
}());
exports.MerkleTree = MerkleTree;
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
exports.default = MerkleTree;
