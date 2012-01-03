static char rcsid[] = "$Id$";

/*
 * big-endianness: bit at index (0+fromIdx) will be the most
 * significant bit in the returned integer value.
 *
 * "fromIdx" must be a valid index in the vector. "fromIdx + numBits"
 * must be <= size of vector. (in other words, "fromIdx + numBits - 1"
 * must be a valid index in the vector.
 */
int boolVectorToInt(const vector<bool> &boolVector,
                    const unsigned int fromIdx,
                    const unsigned int numBits)
{
    int val = 0;

    assert (numBits <= 32);
    assert ((fromIdx + numBits) <= boolVector.size());

    for (int bitNum = fromIdx; bitNum < (fromIdx + numBits); ++bitNum) {
        bool b = boolVector[bitNum];
        if (b) {
            val |= (1 << ((numBits + fromIdx) - bitNum - 1));
        }
        else {
            val &= ~(1 << ((numBits + fromIdx) - bitNum - 1));
        }
    }

    return val;
}


using namespace std;

int testCharArrayToFromBoolVectorConversions()
{
    const int len = 16;
    unsigned char a[] = "AS";
    vector<bool> bv(30);

    charArrayToBoolVector(a, len, bv);

    for (int i = 0; i < len; i++) {
        if ((i % 8) == 0) {
            cout << endl;
        }
        cout << i << " " << bv[i] << endl;
    }

    cout << ("\nreverse...\n\n");

    unsigned char *result = boolVectorToCharArray(bv);
    cout << result << endl;
    return 0;
}

/* convert the char array representation of a bit string to a bool
 * vector representation. assuming big-endianness.
 *
 * "numBits" is the total number of bits in the bit stream
 *
 * examples:
 * "charArray" | "numBits" | output boolVector (starting @ idx zero)
 * "AS"        |  4        | 0 1 0 0
 * ...         |  8        | 0 1 0 0 0 0 0 1
 * ...         |  13       | 0 1 0 0 0 0 0 1  0 1 0 1 0
 * ...         |  16       | 0 1 0 0 0 0 0 1  0 1 0 1 0 0 1 1
 */
void charArrayToBoolVector(const unsigned char* charArray,
                           const unsigned int numBits,
                           vector<bool> &boolVector)
{
    int numChars = numBits / 8;

    assert (numBits > 0);

    if ((numBits % 8) != 0) {
        numChars += 1;
    }

    int bitNum = 0;

    for (int charNum = 0; charNum < numChars; ++charNum) {
        // grab the char
        unsigned char c = charArray[charNum];

        for (int shiftNum = 7; (bitNum < numBits) && (shiftNum > -1); --shiftNum) {
            bool b = c & (1 << shiftNum);
            boolVector[bitNum] = b;
            bitNum++;
        }
    }

    return;
}

/* the opposite of charArrayToBoolVector().
 *
 * caller responsible for freeing the returned array.
 */
unsigned char* boolVectorToCharArray(const vector<bool> &boolVector)
{
    int numBits = boolVector.size();
    int numChars = numBits / 8;

    assert (numBits > 0);

    if ((numBits % 8) != 0) {
        numChars += 1;
    }

    unsigned char* charArray = (unsigned char*)calloc(numChars, 1);
    int bitNum = 0;

    for (int charNum = 0; charNum < numChars; ++charNum) {
        unsigned char c = 0;

        for (int shiftNum = 7; (bitNum < numBits) && (shiftNum > -1); --shiftNum) {
            bool b = boolVector[bitNum];
            if (b) {
                c |= (1 << shiftNum);
            }
            else {
                c &= ~(1 << shiftNum);
            }
            bitNum++;
        }

        charArray[charNum] = c;
    }

    return charArray;
}
