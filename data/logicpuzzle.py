import json
import os
from pathlib import Path

class LogicPuzzle(object):
    """docstring for LogicPuzzle."""
    def __init__(self):
        super(LogicPuzzle, self).__init__()
        self.ID = -1
        self.url = ''
        self.clues = []
        self.domain = {}
        self.title = ''
        self.user = ''
        self.diffulty = '' 
        self.problem = []

    def toDict(self):
        puzzleDict = {
            "url": self.url,
            "id": self.ID,
            "title": self.title,
            "difficulty": self.diffulty,
            "types": self.domain,
            "clues": self.clues+ self.problem
        }
        return puzzleDict

    def downloadPuzzle(self, folderpath='', filename=''):
        # directory path
        dirpath = ''
        # filename
        fn = ''
        print('Downloading problem ...',str(self.ID) )
        if not folderpath:
            srcpaht = Path().cwd()
            dirpath = srcpaht.parent /  'problems'
            if not dirpath.exists():
                dirpath.mkdir()
        else:
            print("Folder does not exist and will be created using path : "  % (folderpath))
            dirpath = Path(folderpath)
            if not dirpath.exists():
                dirpath.mkdir()
        
        if not filename:
            fn = "problem_%s.json" % (str(self.ID))
        
        downloadpath = dirpath / fn

        if downloadpath.exists():
            raise Exception("File already exists : %s" % (downloadpath))
        
        puzzleDict = self.toDict()
        with downloadpath.open('w') as json_file:
            json.dump(puzzleDict, json_file, indent=4)


        
