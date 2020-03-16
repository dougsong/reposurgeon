// Generate vivid but obscuring replacements from input strings.
//
// The reason to do this rather that just generating hashes is that
// we want names that are readily distinguuishable by an unaided
// baseline-human brain.  This code was originally written for
// a fantasy game.

package main

// SPDX-License-Identifier: BSD-2-Clause

import (
	"fmt"
	"math"
)

var color, item []string
var ncolors, nitems int
var phi float64
var seenStrings map[string]string

func init() {
	phi = (1 + math.Sqrt(5)) / 2

	color = []string{
		//  "Adamant",          // 3 syllables
		"Amber",
		"Argent",
		"Amethyst", // 3 syllables
		"Ancient",
		"Autumn",
		"Azure",
		"Beryl",
		//  "Black",            // Same as `Jet'
		"Blazing",
		"Bloodstone",
		//  "Blue",             // Same as `Azure'
		"Bronze",
		"Cerulean", // 4 syllables
		"Cloud",
		"Copper",
		"Coral",
		"Crimson",
		"Crystal",
		"Dancing",
		"Dawn",
		"Death",
		"Desert",
		"Diamond",
		"Ebony",
		"Electrum", // 3 syllables
		//   "Elven",            // Won't work with "Kraken", "Cannon", etc.
		"Emerald",   // 3 syllables
		"Enchanted", // 3 syllables
		"Exalted",   // 3 syllables
		//   "Fiery",           // Collides with "Blazing"
		"Forest",
		"Flying",
		"Garnet",
		"Ghost",
		"Glittering", // 3 syllables
		"Glorious",
		"Golden",
		"Ice",
		"Iron",
		"Island",
		"Ivory",
		"Jade",
		"Jasper",
		"Jet",
		"Lake",
		"Lapis",
		"Leaping",
		"Lightning",
		"Lucky",
		"Malachite", // 3 syllables
		"Marble",
		"Midnight",
		"Mist",
		"Mithril",
		"Moonstone",
		"Mountain",
		"Mystic",
		"Obsidian", // 4 syllables
		"Ocean",
		"Onyx",
		"Opal",
		"Pearl",
		"Perilous", // 3 syllables
		"Plains",
		"Platinum", // 3 syllables
		"Quartz",
		"Radiant",
		"Rainbow",
		//   "Red",             // collides with "Crimson"
		"Rising",
		"Royal",
		"Ruby",
		"Runic",
		"Sable",
		"Sacred",
		"Sapphire",
		"Shadow",
		"Singing",
		"Sky",
		"Spring",
		"Summer",
		"Stone",
		"Storm",
		"Sun",
		"Swift",
		"Topaz",
		"Turquoise",
		"Umber",
		"Valiant",
		"White",
		"Wind",
		"Winter",
		"Verdant",
		"Vitrine",
	}

	item = []string{
		"Angel",
		"Axe",
		"Bear",
		"Bell",
		"Boar",
		"Bolo", // obscure
		"Bolt",
		"Cannon",
		"Centaur",
		"Chalice",
		"Citadel", // 3 syllables
		"Claymore",
		"Cobra",
		"Crag",
		"Crossbow",
		"Crown",
		"Dagger",
		"Dart",
		"Deer",
		"Demon",
		"Dirk",
		"Discus",
		"Dolphin",
		"Dragon",
		"Drum",
		"Eagle",
		"Falchion", // obscure
		"Falcon",
		"Fan",
		"Fang",
		"Flail",
		"Flower",
		"Flute",
		"Fox",
		"Gauntlet",
		//    "Goddess",         // redundant with "Sacred"
		"Gorget",
		"Greave",
		"Gryphon",
		"Halberd",
		"Hammer",
		"Harp",
		"Hawk",
		"Heart",
		"Helm",
		"Hound",
		"Horn",
		"Horse",
		"Hydra",
		"Jaguar",
		"Javelin",
		"Kraken",
		//    "Kris",             // obscure
		"Kukhri",
		"Lance",
		"Leopard",
		"Lion",
		"Lizard",
		"Lynx",
		"Longbow",
		"Mace",
		"Mantis",
		"Mirror",
		"Orb",
		"Pagoda", // Three syllables
		"Panther",
		"Phoenix",
		"Pike",
		"Pyramid",
		"Rapier",
		"Raven",
		"Saber",
		"Scarab",
		"Scepter",
		"Scorpion",
		"Serpent",
		"Shield",
		"Shining",
		"Sigil",
		//   "Silver",             // Conflicts with "Argent"
		"Shrine",
		"Skull",
		"Spear",
		"Spider",
		"Staff",
		"Stag",
		"Star",
		"Swan",
		"Sword",
		"Throne",
		"Tiger",
		"Torc",
		"Tower",
		"Trident",
		"Tusk",
		"Wand",
		//    "Warrior",         // 3 syllables
		"Wheel",
		"Wizard",
		"Wolf",
		"Wyvern",
	}

	// More adjectives:
	//    "Alabaster",
	//    "Carnelian",       // 4 syllables
	//    "Citrine",
	//    "Indigo",
	//    "Lambent",         // obscure
	//    "Painted",
	//    "Purple",
	//    "Radiant",         // 3 syllables; collides with "Shining"
	//    "Screaming",
	//    "Serpentine",
	//    "Solar",
	//    "Thunder",         // Collides with "Lightning"
	//    "Tourmaline",      // 3 syllables
	//    "Vermillion",      // 4 syllables
	//    "Viridian",        // 4 syllables
	//    "Whirling",

	// More nouns:
	//    "Aurochs"
	//    "Bison",
	//    "Claw",            // Collides with "Talon"
	//    "Glass",           // Collides with "Vitrine"
	//    "Moon",            // Collides with "Solar" and "Moonstone"
	//    "Assegai",         // 3 syllables
	//    "Ballista",        // 3 syllables
	//    "Bardiche",        // obscure
	//    "Cauldron",        // Possible conflict with "Pauldron"
	//    "Cestus",          // obscure
	//    "Coyote",          // 3 syllables
	//    "Elephant",        // 3 syllables
	//    "Glaive"           // obscure
	//    "Katana",          // 3 syllables
	//    "Mammoth",
	//    "Manticore",       // 3 syllables
	//    "Morningstar",     // 3 syllables
	//    "Naginata",        // 4 syllables
	//    "Nanchaku",        // 3 syllables
	//    "Pauldron",        // obscure
	//    "Pegasus",         // 3 syllables
	//    "Sai",             // obscure
	//    "Salamander",      // 4 syllables
	//    "Scimitar",        // 3 syllables
	//    "Shuriken",        // 3 syllables
	//    "Seal",
	//    "Sickle",
	//    "Sphere",          // collides with "Orb"
	//    "Talon",
	//    "Temple",          // collides with Shrine
	//    "Unicorn",         // 3 syllables

	ncolors = len(color)
	nitems = len(item)
	seenStrings = make(map[string]string)
}

// Choose a prime close to (ncolors * nitems) / phi, where phi is the
// Golden Section ratio.  This is supposed to give the scramble better
// `randomness' properties.
// Good primes are at https://en.wikipedia.org/wiki/List_of_prime_numbers
const modulus = 5333

// scramble chooses a semi-random number in the wheel range
func scramble(n int) int {
	return (modulus * n) % (len(color) * len(item))
}

// fancyName Return fanciful name corresponding to number n.
func fancyName(n int) string {
	n = scramble(n)
	m := int(n / (ncolors * nitems))
	name := color[int(n%ncolors)] + item[int(n/ncolors)%nitems]
	if m > 0 {
		name += fmt.Sprintf("%d", m)
	}
	return name
}

func obscureString(s string) string {
	v, ok := seenStrings[s]
	if ok {
		return v
	}
	v = fancyName(len(seenStrings) + 1)
	seenStrings[s] = v
	return v
}
