#!/usr/bin/env python
# -*- coding: utf-8 -*-

#Copyright © 2004-2006 Alexandre Muñiz
#
#Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
#
#The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
#
#THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

'''This is a module to find the minimal succinct cover of a set of polyominoes or other polyforms. The minimal succinct cover is a set of polyforms with smallest area for which every polyform in the set being covered can be placed in exactly one position. You can see http://xprt.net/~munizao/polycover for more info, although chances are, if you've obtained this code, you already have. See the last line of this file for an example of how to use this code'''

spew_info = False #If you change this to True, we'll spew info that should help to determine roughly how long it will take the program to run. 

from copy import *

# Import Psyco if available for a slight speedup
try:
    import psyco
    psyco.full()
except ImportError:
    pass

class Spectrum(dict):
    '''A multiset of polyforms.'''
    #This is a hotspot.
    def __add__(self, other):
        out = Spectrum({})
        for key, value in self.items():
            x = out[key] = value + other[key]
            if  x > 1:
                out.is_legal = False
                return out
        return out

    def __radd__(self, other):
        return self

    def is_cover(self):
        for i in self.values():
            if i != 1:
                return False
        return True

    is_legal = True

    def increment_value(self, key):
        self[key] +=1
        if self[key] > 1:
            self.is_legal = False
    
    @classmethod
    def new_spectrum(cls, pset, initform=None):
        out = cls.fromkeys(pset, 0)
        if initform:
            out[initform] += 1
        out.piece_size = len(next(iter(out.keys())))
        return out

# currently, due to the way the best cover algorithm works, this is broken.
class DoubleCoverSpectrum(Spectrum):
    def __add__(self, other):
        out = Spectrum({})
        for key, value in self.items():
            x = out[key] = value + other[key]
            if  x > 2:
                out.is_legal = False
                return out
        return out
    def is_cover(self):
        for i in self.values():
            if i != 2:
                return False
        return True
    def increment_value(self, key):
        self[key] +=1
        if self[key] > 2:
            self.is_legal = False

class Poly(tuple):
    '''Base polyomino class.'''
    def __eq__(self, other):
        return tuple.__eq__(self.canonicalize(), other.canonicalize())
    def __ne__(self, other):
        return tuple.__ne__(self.canonicalize(), other.canonicalize())
    def __gt__(self, other):
        return tuple.__gt__(self.canonicalize(), other.canonicalize())
    def __ge__(self, other):
        return tuple.__ge__(self.canonicalize(), other.canonicalize())
    def __lt__(self, other):
        return tuple.__lt__(self.canonicalize(), other.canonicalize())
    def __le__(self, other):
        return tuple.__le__(self.canonicalize(), other.canonicalize())
    def __hash__(self):
        return tuple.__hash__(self.canonicalize())

    # This function, especially the list comprehension, is a hotspot,
    # and has been slightly optimized for speed.
    def canonpos(self):
        '''Determine the canonical position of a polyform in the plane.'''
        poly = list(self)
        poly.sort()
        if poly[0] == (0,0):
            return Poly(poly)
        x_min, y_min = poly[0]
        return Poly([(x - x_min, y - y_min) for x, y in poly])

        
    is_canonical = False
    spectrum_class = Spectrum
    spectrum = None
    
    def canonicalize(self):
        '''Cache canonicalization.'''
        if self.is_canonical:
            return self
        else:
            return self.canonpos()
        
    connections = [lambda x_y16 : (x_y16[0] + 1, x_y16[1]),
                   lambda x_y17 : (x_y17[0], x_y17[1] + 1),
                   lambda x_y18 : (x_y18[0] - 1, x_y18[1]),
                   lambda x_y19 : (x_y19[0], x_y19[1] - 1)]

    def enlargements(self):
        '''A generator yielding all polyforms that can be made by adding a cell adjacent to this polyform.''' 
        used_neighbors = set()
        for cell in self:
            for i in self.connections:
                neighbor = i(cell)
                if neighbor not in self and neighbor not in used_neighbors:
                    used_neighbors.add(neighbor)
                    out = list(self)
                    out.append(neighbor)
                    out.sort()
                    out = self.__class__(out)
                    yield (neighbor, out)

    def enlarge_spectrum(self, newcell):
        '''Add to the spectrum the polyforms that include the cell being added.'''
        if not self.spectrum:
            return None
        test_poly_list = [(newcell,)]
        for test_poly in test_poly_list:
            if len(test_poly) < self.spectrum.piece_size:
                for (test_newcell, test_enlarged) in self.__class__(test_poly).enlargements():
                    if test_newcell in self:
                        if tuple(test_enlarged) not in test_poly_list:
                            if len(test_enlarged) <= self.spectrum.piece_size:
                                test_poly_list.append(tuple(test_enlarged))
                                if len(test_enlarged) == self.spectrum.piece_size:
                                    test_canon = test_enlarged.canonicalize()
                                    self.spectrum.increment_value(test_canon)
                                    if not self.spectrum.is_legal:
                                        return

    def clone_with_spectrum(self, pset):
        new_pws = self.__class__(copy(self))
        new_pws.spectrum = self.spectrum_class.new_spectrum(pset, new_pws)
        new_pws.size = len(new_pws)
        return new_pws

#a dict to cache correspondences between polyominoes and their canonical form. This is time-useful but space-problematic so as a compromise, only small polyominoes go in.
canon_dict = {}
            
class SymPoly(Poly):
    '''Polyforms with symmetries defined. Classes for specific kinds of polyforms should subclass this.''' 
    syms = [lambda x_y75 : ( x_y75[0],  x_y75[1])]
    def canonicalize(self):
        if self.is_canonical:
            return self
        
        symforms = []
        min_symform = None
        for sym in self.syms:
            curr_symform = self.__class__([sym(x) for x in self]).canonpos()
            t_curr_symform = tuple(curr_symform)
            if len(self) < 8:
                if t_curr_symform in canon_dict:
                    return canon_dict[t_curr_symform]
            symforms.append(t_curr_symform)
            if not min_symform or curr_symform < min_symform:
                min_symform = curr_symform
        
        out = self.__class__(min_symform)
        
        if len(self) < 8:
            for i in symforms:
                canon_dict[i] = out
                
        out.is_canonical = True
        out.spectrum = self.spectrum
        return out
    
    @classmethod
    def n_ominoes(cls, n):
        '''Returns a list of n-ominoes, that is, shapes with n connected cells.'''
        n_omino_list = []     
        for i in range(n):
            prev_n_omino_list = n_omino_list
            n_omino_list = []            
            if i == 0:
                n_omino_list.append(cls(((0,0),)))
            else:
                for poly in prev_n_omino_list:
                    for enlargement in poly.enlargements():
                        newpoly = enlargement[1].canonicalize()
                        if newpoly not in n_omino_list:
                            n_omino_list.append(newpoly)

        return n_omino_list

    @classmethod
    def cover_report(cls, n):
        '''Generate a report with information about a set of polyominoes and its minimal succinct cover.'''
        om = cls.n_ominoes(n)
        print("Type: %s, Size: %s" %(cls.__name__, n))
        print("Number in Set: %s" %len(om))
        pieces, cover = Polyset(om).get_best_cover(n)
        print("Minimal cover size: %s" %cover.size())
        print("Number of pieces in minimal cover: %s" %len(cover))
        print(cover)
        return pieces, cover

class TwoSidedPolyomino(SymPoly):
    '''The standard polyomino variant, where all reflections and rotations of a polyomino are equivalent.

    This should be used as the default polyform class wherever it is appropriate to use a default.''' 
    syms = [lambda x_y20 : ( x_y20[0],  x_y20[1]),
            lambda x_y21 : ( x_y21[0], -x_y21[1]),
            lambda x_y22 : (-x_y22[0],  x_y22[1]),
            lambda x_y23 : (-x_y23[0], -x_y23[1]),
            lambda x_y24 : ( x_y24[1],  x_y24[0]),
            lambda x_y25 : ( x_y25[1], -x_y25[0]),
            lambda x_y26 : (-x_y26[1],  x_y26[0]),
            lambda x_y27 : (-x_y27[1], -x_y27[0])]

class OneSidedPolyomino(SymPoly):
    '''A polyomino variant where only rotations are equivalent; reflections are considered to be distinct.'''
    syms = [lambda x_y28 : ( x_y28[0],  x_y28[1]),
            lambda x_y29 : ( x_y29[1], -x_y29[0]),
            lambda x_y30 : (-x_y30[0], -x_y30[1]),
            lambda x_y31 : (-x_y31[1],  x_y31[0])]

class FixedPolyomino(SymPoly):
    '''A polyomino variant where rotations and reflections are considered distinct.'''
    syms = [lambda x_y76 : ( x_y76[0],  x_y76[1])]

class RectangularPolyomino(SymPoly):
    '''A polyomino variant where cells have rectangular symmetry.'''
    syms = [lambda x_y32 : ( x_y32[0],  x_y32[1]),
            lambda x_y33 : ( x_y33[0], -x_y33[1]),
            lambda x_y34 : (-x_y34[0],  x_y34[1]),
            lambda x_y35 : (-x_y35[0], -x_y35[1])]

class RhombicPolyomino(SymPoly):
    '''A polyomino variant where cells have rhombic symmetry.'''
    syms = [lambda x_y36 : ( x_y36[0],  x_y36[1]),
            lambda x_y37 : ( x_y37[1],  x_y37[0]),
            lambda x_y38 : (-x_y38[1], -x_y38[0]),
            lambda x_y39 : (-x_y39[0], -x_y39[1])]

class PolyKing(TwoSidedPolyomino):
    '''A polyomino variant where diagonally adjacent cells are considered connected.'''
    #We add the diagonals
    connections =  Poly.connections + [lambda x_y : (x_y[0] + 1, x_y[1] + 1),
                                       lambda x_y1 : (x_y1[0] - 1, x_y1[1] + 1),
                                       lambda x_y2 : (x_y2[0] - 1, x_y2[1] - 1),
                                       lambda x_y3 : (x_y3[0] + 1, x_y3[1] - 1)]

class OneSidedPolyhex(SymPoly):
    '''A polyform of cells in a hexagonal lattice, with rotations considered equivalent, and reflections distinct.'''
    connections = [lambda x_y40 : (x_y40[0] + 1, x_y40[1]),
                   lambda x_y41 : (x_y41[0], x_y41[1] + 1),
                   lambda x_y42 : (x_y42[0] - 1, x_y42[1]),
                   lambda x_y43 : (x_y43[0], x_y43[1] - 1),
                   lambda x_y44 : (x_y44[0] + 1, x_y44[1] + 1),
                   lambda x_y45 : (x_y45[0] - 1, x_y45[1] - 1)]
    
    syms = [lambda x_y46 : ( x_y46[0],  x_y46[1]),
            lambda x_y47 : ( x_y47[1], x_y47[1] - x_y47[0]),
            lambda x_y48 : (x_y48[1] - x_y48[0], -x_y48[0]),
            lambda x_y49 : (-x_y49[0],  -x_y49[1]),
            lambda x_y50 : (-x_y50[1],  x_y50[0] - x_y50[1]),
            lambda x_y51 : (x_y51[0] - x_y51[1],  x_y51[0])]

class TwoSidedPolyhex(OneSidedPolyhex):
    '''A polyform of cells in a hexagonal lattice, with rotations and reflections considered equivalent.'''
    syms = OneSidedPolyhex.syms + [lambda x_y4 : (x_y4[1] - x_y4[0], x_y4[1]),
                                   lambda x_y5 : (x_y5[1], x_y5[0]),
                                   lambda x_y6 : (x_y6[0], x_y6[0] - x_y6[1]),
                                   lambda x_y7 : (x_y7[0] - x_y7[1], -x_y7[1]),
                                   lambda x_y8 : (-x_y8[1], -x_y8[0]),
                                   lambda x_y9 : (-x_y9[0], x_y9[1] - x_y9[0])] #reflections



class CheckerPoly(Poly):
    '''Base class for polyominos where squares have a checkered coloring pattern.'''
#Sometimes it's convenient to use 1,0 to denote colors, other times 1,-1
    @staticmethod
    def cell_color (x, y):
        return (x % 2) ^ (y % 2)

    @staticmethod
    def cell_parity(x, y):
        return 2 * cell_color((x,y)) - 1

    def canonpos(self):
        '''Determine the canonical position of a checkered polyomino. Colors are preserved.'''
        o1 = list(self)
        o1.sort()
        if o1[0] == (0,0):
            return CheckerPoly(o1)
        color =  self.cell_color(o1[0][0], o1[0][1])
            
        x_min, y_min = o1[0]
        return CheckerPoly([(x - x_min + color, y - y_min) for x, y in o1])

class TwoSidedCheckerPolyomino(CheckerPoly, TwoSidedPolyomino):
    '''A polyomino variant with squares with a checkered coloring pattern; different colorings of a polyomino are considered distinct.'''


class PolyStick(CheckerPoly, SymPoly):
    '''A polyform of connected edges in a square lattice.'''
    connections = [lambda x_y52 : (x_y52[0] + 1, x_y52[1]),
                   lambda x_y53 : (x_y53[0], x_y53[1] + 1),
                   lambda x_y54 : (x_y54[0] - 1, x_y54[1]),
                   lambda x_y55 : (x_y55[0], x_y55[1] - 1),
                   lambda x_y56 : ((x_y56[0] + 1, x_y56[1] + CheckerPoly.cell_parity(x_y56[0],x_y56[1]))),
                   lambda x_y57 : ((x_y57[0] - 1, x_y57[1] - CheckerPoly.cell_parity(x_y57[0],x_y57[1]))),]
    
    syms =  [lambda x_y58 : ( x_y58[0],  x_y58[1]),
             lambda x_y59 : ( x_y59[1],  x_y59[0]),
             lambda x_y60 : (-x_y60[1], -x_y60[0]),
             lambda x_y61 : (-x_y61[0], -x_y61[1]),         
             lambda x_y62 : (-x_y62[0],  x_y62[1] + 1),
             lambda x_y63 : (-x_y63[1],  x_y63[0] + 1),
             lambda x_y64 : ( x_y64[1], -x_y64[0] + 1),
             lambda x_y65 : ( x_y65[0], -x_y65[1] + 1),]

class OneSidedPolyiamond(CheckerPoly, SymPoly):
    '''One sided polyforms in a triangular lattice.'''
    @staticmethod
    def cell_parity(x, y):
        d = (x + y) % 3
        if d == 0:
            parity = 1
        elif d == 1:
            parity = -1
        else:
            parity = None
        return parity
        
    @staticmethod
    def cell_color(x, y):
        color = (x + y) % 3
        return color

    connections = [lambda x_y66 : (x_y66[0] + OneSidedPolyiamond.cell_parity(x_y66[0],x_y66[1]), x_y66[1]),
                   lambda x_y67 : (x_y67[0], x_y67[1] + OneSidedPolyiamond.cell_parity(x_y67[0],x_y67[1])),
                   lambda x_y68 : (x_y68[0] - OneSidedPolyiamond.cell_parity(x_y68[0],x_y68[1]), x_y68[1] - OneSidedPolyiamond.cell_parity(x_y68[0],x_y68[1]))]
    syms = [ lambda x_y69 : (x_y69[0], x_y69[1]),
             lambda x_y70 : (x_y70[1] - x_y70[0], -x_y70[0]),
             lambda x_y71 : (-x_y71[1], x_y71[0] - x_y71[1]),
             # 180 rotations
             lambda x_y72 : (-x_y72[0] + 1, -x_y72[1]),
             lambda x_y73 : (x_y73[0] - x_y73[1] + 1, x_y73[0]),
             lambda x_y74 : (x_y74[1] + 1, x_y74[1] - x_y74[0])]

class TwoSidedPolyiamond(OneSidedPolyiamond):
    '''Two sided polyforms in a triangular lattice.'''
    syms = OneSidedPolyiamond.syms + [lambda x_y10 : (x_y10[1], x_y10[0]),
                                      lambda x_y11 : (-x_y11[0], x_y11[1] - x_y11[0]),
                                      lambda x_y12 : (x_y12[0] - x_y12[1], -x_y12[1]),
                                      lambda x_y13 : (-x_y13[1], -x_y13[0] + 1),
                                      lambda x_y14 : (x_y14[0], x_y14[0] - x_y14[1] + 1),
                                      lambda x_y15 : (x_y15[1] - x_y15[0], x_y15[1] + 1)] 


             
# currently, due to the way the best cover algorithm works, this is broken.
class DoubleTwoSidedPolyomino(TwoSidedPolyomino):
    spectrum_class = DoubleCoverSpectrum

# Not actually a set but a list. The order that we iterate through it can be important for speed.
class Polyset(list):
    '''A set of polyforms.'''
    def size(self):
        '''The total number of cells in all polyforms in the set'''
        return sum((len(x) for x in self))
    
    def largest(self):
        '''A tuple containing the size of a largest piece and a largest piece'''
        return max(((len(x),x) for x in pieces))

    def most_prolific(self):
        '''A tuple containing the largest number of polyforms in our target set that can be placed in a piece and said piece'''
        return max(((sum(x.spectrum.values()),x) for x in pieces))

    def most_efficient(self):
        '''A tuple containing the highest ratio of pieces in our target set that can be placed in a piece to the size of the piece, and said piece'''
        return max(((float(sum(x.spectrum.values())) / len(x),x) for x in pieces))
    
    def get_cover_pieces(self):
        '''The set of polyforms that are legal pieces for succinct covers.'''
        cover_pieces = [i.clone_with_spectrum(self) for i in self]
        for i in cover_pieces:
            for newcell, new_cp in i.enlargements():
                new_cp.spectrum = copy(i.spectrum)
                new_cp.enlarge_spectrum(newcell)
                if new_cp.spectrum.is_legal:
                    new_cp = new_cp.canonicalize()
                    if new_cp not in cover_pieces:
                        cover_pieces.append(new_cp)
                        if spew_info and len(cover_pieces) % 1000 == 0:
                            #If the two numbers printed are converging, the function might not take an inordinate amount of time to complete.
                            print("piece %s of %s" %(cover_pieces.index(i), len(cover_pieces)))
        return cover_pieces
    # A cover piece that is the same size or larger than another cover piece with the same spectrum is redundant for the purpose of finding a minimal succinct cover.
    def trim_cover_pieces(self, pieces):
        '''Remove redundant cover pieces.'''
        spectrum_dict = {}
        out_pieces = []
        for i in pieces:
            spec_items = tuple(i.spectrum.items())
            best_size = spectrum_dict.get(spec_items)
            if (not best_size) or best_size > len(i):
                spectrum_dict[spec_items] = len(i)
                out_pieces.append(i)
        return out_pieces
    
    # The algorithm here is a bit clever. Naively, one might think we'd have to search the entire power set of the set of cover pieces to find our minimal succinct cover. Instead we can, for each polyomino, iterate through the cover pieces it is contained by (and skip down the list of polyominoes if one of the cover pieces we have already has it.) We speed things up a little by sorting the "covered by" list and cutting off branches where we have exceeded the size of the best cover found so far. This way instead of being O(2^number of cover pieces) we are, roughly, O((number of pieces / number of polyominoes)^number of polyominoes). I *think* this is an improvement.
    def get_best_cover(self, min_omino_size=0):
        '''Get the minimal succinct cover of the set.'''
        best_size = self.size() + 1
        best_cover = None
        pieces1 = self.get_cover_pieces()
        print("Number of legal cover pieces: %s" %len(pieces1))
        pieces = self.trim_cover_pieces(pieces1)
        if spew_info:
            print("Number of cover pieces after trimming: %s" %len(pieces))
        for i in self:
            i.contained_by = [x for x in pieces if x.spectrum[i]]
            i.contained_by.sort(key = lambda x : sum(x.spectrum.values()))
        self.sort(key = lambda x : len(x.contained_by))
        
        # this next bit ensures that we won't ever look at a piece that is already in our partial cover. It therefore breaks 2-succinct covers, but those are broken anyway.
        already_seen_pieces = set()
        for i in self:
            for j in i.contained_by:
                if j in already_seen_pieces:
                    i.contained_by.remove(j)
                else:
                    already_seen_pieces.add(j)
                    
        cp_indices = [0]
        while True:
            partial = Polyset([self[i].contained_by[cp_indices[i]] for i in range(len(cp_indices)) if not cp_indices[i] is None])
            spectrum = sum([x.spectrum for x in partial], None)
            size = partial.size()
            
            if spectrum.is_legal and size < best_size:
                if spectrum.is_cover():
                    best_cover = copy(cp_indices)
                    best_size = size
                else:
                    while len(cp_indices) < len(self) and spectrum[self[len(cp_indices) -1]] == 1:
                        cp_indices.append(None)
                    cp_indices[-1] = 0
                    
            if not spectrum.is_legal or not size < best_size:
                cp_indices[-1] += 1
                while cp_indices[-1] is None or cp_indices[-1] == len(self[len(cp_indices) -1].contained_by):
                        cp_indices.pop()
                        if cp_indices == []:
                            return pieces1, Polyset([self[i].contained_by[best_cover[i]] for i in range(len(best_cover)) if not best_cover[i] is None])
                        if not cp_indices[-1] is None:
                            cp_indices[-1] += 1

if __name__ == '__main__':
    #Pick a class and size of polyform, and change the following line to suit.
    pieces, cover = OneSidedPolyomino.cover_report(5)
