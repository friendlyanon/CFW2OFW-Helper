using System;
using System.IO;
using System.Net;
using System.Xml;
using System.Text;
using System.Reflection;
using System.Collections;
using System.Diagnostics;
using System.Collections.Generic;
using System.Security.Cryptography;
using System.Text.RegularExpressions;

namespace CFW2OFW
{

    class G
    {
        public static Queue<string> patchURLs = new Queue<string>();
        public static Queue<string> patchFNames = new Queue<string>();
        public static String gameName = "";
        public static String newID = "";
        public static String input = "";
        public static String ID = "";
        public static String newVer = "";
        public static KeyValuePair<int, int> verOffset;
        public static XmlDocument xmlDoc = new XmlDocument();
        public static string outputDir = "";
        public static string targetDir = "";
        public static readonly string currentDir = Path.GetDirectoryName(Assembly.GetEntryAssembly().Location);
        public static readonly string makeNpdata = currentDir + "\\make_npdata.exe";
        public static readonly string patchPath = currentDir + "\\patch";
        public static readonly string DECPath = patchPath + "\\decrypted.data";
        public static readonly WebClient wc = new WebClient();
        public static uint FailedPatches = 0;
        public static void Exit(string msg)
        {
            Console.WriteLine(msg);
            Console.Write("Press any key to exit . . .");
            Console.ReadKey(true);
            Environment.Exit(0);
        }
    }

    public partial class PS3
    {
        private readonly static byte[] AesKey = new byte[16] {
            0x2E, 0x7B, 0x71, 0xD7, 0xC9, 0xC9, 0xA1, 0x4E,
            0xA3, 0x22, 0x1F, 0x18, 0x88, 0x28, 0xB8, 0xF8
        };

        private static byte[] PKGFileKey;

        private static uint uiEncryptedFileStartOffset;

        private static Boolean IncrementArray(ref byte[] sourceArray, int position)
        {
            if (sourceArray[position] == 0xFF)
            {
                if (position != 0)
                {
                    if (IncrementArray(ref sourceArray, position - 1))
                    {
                        sourceArray[position] = 0x00;
                        return true;
                    }
                    else return false;
                }
                else return false;
            }
            else
            {
                sourceArray[position] += 0x01;
                return true;
            }
        }

        public class PKGExtract
        {
            private static string HexStringToAscii(string HexString)
            {
                try
                {
                    StringBuilder StrValue = new StringBuilder();
                    while (HexString.Length > 0)
                    {
                        StrValue.Append(Convert.ToChar(Convert.ToUInt32(HexString.Substring(0, 2), 16)).ToString());
                        HexString = HexString.Substring(2, HexString.Length - 2);
                    }
                    return StrValue.ToString().Replace("\0", "");
                }
                catch (Exception)
                {
                    return null;
                }
            }

            private static string ByteArrayToAscii(byte[] ByteArray, int startPos, int length)
            {
                byte[] byteArrayPhrase = new byte[length];
                Array.Copy(ByteArray, startPos, byteArrayPhrase, 0, byteArrayPhrase.Length);
                string hexPhrase = ByteArrayToHexString(byteArrayPhrase);
                return HexStringToAscii(hexPhrase);
            }

            private static string ByteArrayToHexString(byte[] ByteArray)
            {
                StringBuilder HexString = new StringBuilder();
                for (int i = 0; i < ByteArray.Length; ++i)
                    HexString.Append(ByteArray[i].ToString("X2"));
                return HexString.ToString();
            }

            private static byte[] DecryptData(int dataSize, long dataRelativeOffset, Stream encrPKGReadStream, BinaryReader brEncrPKG)
            {
                int size = dataSize % 16;
                if (size > 0)
                    size = ((dataSize / 16) + 1) * 16;
                else
                    size = dataSize;
                byte[] PKGFileKeyConsec = new byte[size], incPKGFileKey = new byte[PKGFileKey.Length];
                Array.Copy(PKGFileKey, incPKGFileKey, PKGFileKey.Length);
                encrPKGReadStream.Seek(dataRelativeOffset + uiEncryptedFileStartOffset, SeekOrigin.Begin);
                byte[] EncryptedData = brEncrPKG.ReadBytes(size);
                for (long pos = 0; pos < dataRelativeOffset; pos += 16)
                    IncrementArray(ref incPKGFileKey, PKGFileKey.Length - 1);

                for (long pos = 0; pos < size; pos += 16)
                {
                    Array.Copy(incPKGFileKey, 0, PKGFileKeyConsec, pos, PKGFileKey.Length);
                    IncrementArray(ref incPKGFileKey, PKGFileKey.Length - 1);
                }
                byte[] PKGXorKeyConsec = AESEngine.Encrypt(PKGFileKeyConsec, AesKey, AesKey, CipherMode.ECB, PaddingMode.None);
                return XOREngine.XOR(EncryptedData, 0, PKGXorKeyConsec.Length, PKGXorKeyConsec);
            }

            public static void ExtractFiles(string encryptedPKGFileName)
            {
                int twentyMb = 1024 * 1024 * 20;
                UInt64 ExtractedFileOffset = 0, ExtractedFileSize = 0;
                UInt32 OffsetShift = 0;
                long positionIdx = 0;
                
                string WorkDir = $@"{G.outputDir}\{G.ID}\";

                if (!Directory.Exists(WorkDir))
                    Directory.CreateDirectory(WorkDir);

                byte[] FileTable = new byte[320000], dumpFile, firstFileOffset = new byte[4],
                    firstNameOffset = new byte[4], Offset = new byte[8], Size = new byte[8],
                    NameOffset = new byte[4], NameSize = new byte[4], Name = new byte[32];
                byte contentType = 0, fileType = 0;
                bool isFile = false;

                Stream decrPKGReadStream = new FileStream(G.DECPath, FileMode.Open, FileAccess.Read, FileShare.ReadWrite);
                BinaryReader brDecrPKG = new BinaryReader(decrPKGReadStream);

                Stream encrPKGReadStream = new FileStream(encryptedPKGFileName, FileMode.Open, FileAccess.Read, FileShare.ReadWrite);
                BinaryReader brEncrPKG = new BinaryReader(encrPKGReadStream);
                
                decrPKGReadStream.Seek(0, SeekOrigin.Begin);
                FileTable = brDecrPKG.ReadBytes(FileTable.Length);

                Array.Copy(FileTable, 0, firstNameOffset, 0, firstNameOffset.Length);
                Array.Reverse(firstNameOffset);
                uint uifirstNameOffset = BitConverter.ToUInt32(firstNameOffset, 0);

                uint uiFileNr = uifirstNameOffset / 32;

                Array.Copy(FileTable, 12, firstFileOffset, 0, firstFileOffset.Length);
                Array.Reverse(firstFileOffset);
                uint uifirstFileOffset = BitConverter.ToUInt32(firstFileOffset, 0);
                
                decrPKGReadStream.Seek(0, SeekOrigin.Begin);
                FileTable = brDecrPKG.ReadBytes((int)uifirstFileOffset);
                
                if ((int)uiFileNr < 0)
                    G.Exit("An error occured during the extraction operation, because of a decryption error");
                
                for (int ii = 0; ii < (int)uiFileNr; ii++)
                {
                    Array.Copy(FileTable, positionIdx + 8, Offset, 0, Offset.Length);
                    Array.Reverse(Offset);
                    ExtractedFileOffset = BitConverter.ToUInt64(Offset, 0) + OffsetShift;

                    Array.Copy(FileTable, positionIdx + 16, Size, 0, Size.Length);
                    Array.Reverse(Size);
                    ExtractedFileSize = BitConverter.ToUInt64(Size, 0);

                    Array.Copy(FileTable, positionIdx, NameOffset, 0, NameOffset.Length);
                    Array.Reverse(NameOffset);
                    uint ExtractedFileNameOffset = BitConverter.ToUInt32(NameOffset, 0);

                    Array.Copy(FileTable, positionIdx + 4, NameSize, 0, NameSize.Length);
                    Array.Reverse(NameSize);
                    uint ExtractedFileNameSize = BitConverter.ToUInt32(NameSize, 0);

                    contentType = FileTable[positionIdx + 24];
                    fileType = FileTable[positionIdx + 27];

                    Name = new byte[ExtractedFileNameSize];
                    Array.Copy(FileTable, (int)ExtractedFileNameOffset, Name, 0, ExtractedFileNameSize);
                    string ExtractedFileName = ByteArrayToAscii(Name, 0, Name.Length);

                    FileStream ExtractedFileWriteStream = null;
                    
                    if ((fileType == 0x04) && (ExtractedFileSize == 0x00))
                        isFile = false;
                    else
                        isFile = true;
                    
                    byte[] DecryptedData = DecryptData((int)ExtractedFileNameSize, ExtractedFileNameOffset, encrPKGReadStream, brEncrPKG);
                    Array.Copy(DecryptedData, 0, Name, 0, ExtractedFileNameSize);
                    ExtractedFileName = ByteArrayToAscii(Name, 0, Name.Length);

                    if (!isFile)
                    {
                        if (!Directory.Exists(ExtractedFileName))
                            Directory.CreateDirectory(WorkDir + ExtractedFileName);
                    }
                    else
                    {
                        if (File.Exists(WorkDir + ExtractedFileName))
                            File.Delete(WorkDir + ExtractedFileName);
                        ExtractedFileWriteStream = new FileStream(WorkDir + ExtractedFileName, FileMode.CreateNew, FileAccess.ReadWrite, FileShare.ReadWrite);
                    }

                    if (contentType != 0x90 && isFile)
                    {
                        BinaryWriter ExtractedFile = new BinaryWriter(ExtractedFileWriteStream);

                        double division = (double)ExtractedFileSize / twentyMb;
                        UInt64 pieces = (UInt64)Math.Floor(division);
                        UInt64 mod = ExtractedFileSize % (UInt64)twentyMb;
                        if (mod > 0)
                            pieces += 1;

                        dumpFile = new byte[twentyMb];
                        long elapsed = 0;
                        for (UInt64 i = 0; i < pieces; i++)
                        {
                            if ((mod > 0) && (i == (pieces - 1)))
                                dumpFile = new byte[mod];

                            byte[] Decrypted_Data = DecryptData(dumpFile.Length, (long)ExtractedFileOffset + elapsed, encrPKGReadStream, brEncrPKG);
                            elapsed += dumpFile.Length;
                            
                            ExtractedFile.Write(Decrypted_Data, 0, dumpFile.Length);
                        }
                        ExtractedFile.Close();
                    }

                    positionIdx = positionIdx + 32;
                }
                brEncrPKG.Close();
                brDecrPKG.Close();
                
                if (File.Exists(G.DECPath))
                    File.Delete(G.DECPath);
            }
        }

        public class PKGDecrypt
        {
            public static void DecryptPKGFile(string PKGFileName)
            {
                byte[] EncryptedFileStartOffset = new byte[8];

                Stream PKGReadStream = new FileStream(PKGFileName, FileMode.Open, FileAccess.Read, FileShare.ReadWrite);
                BinaryReader brPKG = new BinaryReader(PKGReadStream);
                
                PKGReadStream.Seek(0x07, SeekOrigin.Begin);
                byte pkgType = brPKG.ReadByte();

                switch (pkgType)
                {
                case 0x01:
                    break;
                default:
                    G.Exit("This is not a PS3 PKG.");
                    break;
                }

                PKGReadStream.Seek(0x14, SeekOrigin.Begin);
                byte[] FileChunks = new byte[4];
                FileChunks = brPKG.ReadBytes(FileChunks.Length);
                Array.Reverse(FileChunks);
                uint uiFileChunks = BitConverter.ToUInt32(FileChunks, 0);
                
                PKGReadStream.Seek(0x20, SeekOrigin.Begin);
                EncryptedFileStartOffset = brPKG.ReadBytes(EncryptedFileStartOffset.Length);
                Array.Reverse(EncryptedFileStartOffset);
                uiEncryptedFileStartOffset = BitConverter.ToUInt32(EncryptedFileStartOffset, 0);
                
                PKGReadStream.Seek(0x70, SeekOrigin.Begin);
                PKGFileKey = brPKG.ReadBytes(16);
                byte[] incPKGFileKey = new byte[16];
                Array.Copy(PKGFileKey, incPKGFileKey, PKGFileKey.Length);

                if (File.Exists(G.DECPath))
                    File.Delete(G.DECPath);
                
                FileStream DecryptedFileWriteStream = new FileStream(G.DECPath, FileMode.CreateNew, FileAccess.ReadWrite, FileShare.ReadWrite);
                BinaryWriter bwDecryptedFile = new BinaryWriter(DecryptedFileWriteStream);
                
                PKGReadStream.Seek((int)uiEncryptedFileStartOffset, SeekOrigin.Begin);

                byte[] EncryptedDataList = brPKG.ReadBytes((int)(uiFileChunks * 0x20)),
                    PKGFileKeyConsec = new byte[EncryptedDataList.Length], PKGXorKeyConsec;

                for (int pos = 0; pos < EncryptedDataList.Length; pos += AesKey.Length)
                {
                    Array.Copy(incPKGFileKey, 0, PKGFileKeyConsec, pos, PKGFileKey.Length);
                    IncrementArray(ref incPKGFileKey, PKGFileKey.Length - 1);
                }
                PKGXorKeyConsec = AESEngine.Encrypt(PKGFileKeyConsec, AesKey, AesKey, CipherMode.ECB, PaddingMode.None);
                
                byte[] DecryptedDataList = XOREngine.XOR(EncryptedDataList, 0, PKGXorKeyConsec.Length, PKGXorKeyConsec);

                bwDecryptedFile.Write(DecryptedDataList);

                for (uint i = 0; i < uiFileChunks; i++)
                {
                    uint size = BitConverter.ToUInt32(DecryptedDataList, (int)(i * 0x20) + 4);
                    size = (size & 0x000000FFU) << 24 | (size & 0x0000FF00U) << 8 | (size & 0x00FF0000U) >> 8 | (size & 0xFF000000U) >> 24;
                    size = (size & 0xFFFFFFF0U) + 0x10;
                    byte[] EncryptedDataEntry = brPKG.ReadBytes((int)size);
                    PKGFileKeyConsec = new byte[EncryptedDataEntry.Length];

                    for (int pos = 0; pos < EncryptedDataEntry.Length; pos += AesKey.Length)
                    {
                        Array.Copy(incPKGFileKey, 0, PKGFileKeyConsec, pos, PKGFileKey.Length);
                        IncrementArray(ref incPKGFileKey, PKGFileKey.Length - 1);
                    }
                    PKGXorKeyConsec = AESEngine.Encrypt(PKGFileKeyConsec, AesKey, AesKey, CipherMode.ECB, PaddingMode.None);

                    byte[] DecryptedDataEntry = XOREngine.XOR(EncryptedDataEntry, 0, PKGXorKeyConsec.Length, PKGXorKeyConsec);
                    bwDecryptedFile.Write(DecryptedDataEntry);
                }
                bwDecryptedFile.Close();
            }
        }

        private class AESEngine
        {
            public static byte[] Encrypt(byte[] clearData, byte[] Key, byte[] IV, CipherMode cipherMode, PaddingMode paddingMode)
            {
                MemoryStream ms = new MemoryStream();
                Rijndael alg = Rijndael.Create();
                alg.Mode = cipherMode;
                alg.Padding = paddingMode;
                alg.Key = Key;
                alg.IV = IV;
                CryptoStream cs = new CryptoStream(ms,
                   alg.CreateEncryptor(), CryptoStreamMode.Write);
                cs.Write(clearData, 0, clearData.Length);
                cs.Close();
                byte[] encryptedData = ms.ToArray();
                return encryptedData;
            }
        }

        private class XOREngine
        {
            public static byte[] XOR(byte[] inByteArray, int offsetPos, int length, byte[] XORKey)
            {
                if (inByteArray.Length < offsetPos + length)
                    G.Exit("Combination of chosen offset pos. & Length goes outside of the array to be xored.");
                if ((length % XORKey.Length) != 0)
                    G.Exit("Number of bytes to be XOR'd isn't a mutiple of the XOR key length.");
                int pieces = length / XORKey.Length;
                byte[] outByteArray = new byte[length];
                for (int i = 0; i < pieces; i++)
                    for (int pos = 0; pos < XORKey.Length; pos++)
                        outByteArray[(i * XORKey.Length) + pos] += (byte)(inByteArray[offsetPos + (i * XORKey.Length) + pos] ^ XORKey[pos]);
                return outByteArray;
            }
        }
    }

    static class Program
    {
        static byte[] Crc32(byte[] data)
        {
            var table = new uint[] {
                0x00000000, 0x77073096, 0xEE0E612C, 0x990951BA, 0x076DC419, 0x706AF48F,
                0xE963A535, 0x9E6495A3, 0x0EDB8832, 0x79DCB8A4, 0xE0D5E91E, 0x97D2D988,
                0x09B64C2B, 0x7EB17CBD, 0xE7B82D07, 0x90BF1D91, 0x1DB71064, 0x6AB020F2,
                0xF3B97148, 0x84BE41DE, 0x1ADAD47D, 0x6DDDE4EB, 0xF4D4B551, 0x83D385C7,
                0x136C9856, 0x646BA8C0, 0xFD62F97A, 0x8A65C9EC, 0x14015C4F, 0x63066CD9,
                0xFA0F3D63, 0x8D080DF5, 0x3B6E20C8, 0x4C69105E, 0xD56041E4, 0xA2677172,
                0x3C03E4D1, 0x4B04D447, 0xD20D85FD, 0xA50AB56B, 0x35B5A8FA, 0x42B2986C,
                0xDBBBC9D6, 0xACBCF940, 0x32D86CE3, 0x45DF5C75, 0xDCD60DCF, 0xABD13D59,
                0x26D930AC, 0x51DE003A, 0xC8D75180, 0xBFD06116, 0x21B4F4B5, 0x56B3C423,
                0xCFBA9599, 0xB8BDA50F, 0x2802B89E, 0x5F058808, 0xC60CD9B2, 0xB10BE924,
                0x2F6F7C87, 0x58684C11, 0xC1611DAB, 0xB6662D3D, 0x76DC4190, 0x01DB7106,
                0x98D220BC, 0xEFD5102A, 0x71B18589, 0x06B6B51F, 0x9FBFE4A5, 0xE8B8D433,
                0x7807C9A2, 0x0F00F934, 0x9609A88E, 0xE10E9818, 0x7F6A0DBB, 0x086D3D2D,
                0x91646C97, 0xE6635C01, 0x6B6B51F4, 0x1C6C6162, 0x856530D8, 0xF262004E,
                0x6C0695ED, 0x1B01A57B, 0x8208F4C1, 0xF50FC457, 0x65B0D9C6, 0x12B7E950,
                0x8BBEB8EA, 0xFCB9887C, 0x62DD1DDF, 0x15DA2D49, 0x8CD37CF3, 0xFBD44C65,
                0x4DB26158, 0x3AB551CE, 0xA3BC0074, 0xD4BB30E2, 0x4ADFA541, 0x3DD895D7,
                0xA4D1C46D, 0xD3D6F4FB, 0x4369E96A, 0x346ED9FC, 0xAD678846, 0xDA60B8D0,
                0x44042D73, 0x33031DE5, 0xAA0A4C5F, 0xDD0D7CC9, 0x5005713C, 0x270241AA,
                0xBE0B1010, 0xC90C2086, 0x5768B525, 0x206F85B3, 0xB966D409, 0xCE61E49F,
                0x5EDEF90E, 0x29D9C998, 0xB0D09822, 0xC7D7A8B4, 0x59B33D17, 0x2EB40D81,
                0xB7BD5C3B, 0xC0BA6CAD, 0xEDB88320, 0x9ABFB3B6, 0x03B6E20C, 0x74B1D29A,
                0xEAD54739, 0x9DD277AF, 0x04DB2615, 0x73DC1683, 0xE3630B12, 0x94643B84,
                0x0D6D6A3E, 0x7A6A5AA8, 0xE40ECF0B, 0x9309FF9D, 0x0A00AE27, 0x7D079EB1,
                0xF00F9344, 0x8708A3D2, 0x1E01F268, 0x6906C2FE, 0xF762575D, 0x806567CB,
                0x196C3671, 0x6E6B06E7, 0xFED41B76, 0x89D32BE0, 0x10DA7A5A, 0x67DD4ACC,
                0xF9B9DF6F, 0x8EBEEFF9, 0x17B7BE43, 0x60B08ED5, 0xD6D6A3E8, 0xA1D1937E,
                0x38D8C2C4, 0x4FDFF252, 0xD1BB67F1, 0xA6BC5767, 0x3FB506DD, 0x48B2364B,
                0xD80D2BDA, 0xAF0A1B4C, 0x36034AF6, 0x41047A60, 0xDF60EFC3, 0xA867DF55,
                0x316E8EEF, 0x4669BE79, 0xCB61B38C, 0xBC66831A, 0x256FD2A0, 0x5268E236,
                0xCC0C7795, 0xBB0B4703, 0x220216B9, 0x5505262F, 0xC5BA3BBE, 0xB2BD0B28,
                0x2BB45A92, 0x5CB36A04, 0xC2D7FFA7, 0xB5D0CF31, 0x2CD99E8B, 0x5BDEAE1D,
                0x9B64C2B0, 0xEC63F226, 0x756AA39C, 0x026D930A, 0x9C0906A9, 0xEB0E363F,
                0x72076785, 0x05005713, 0x95BF4A82, 0xE2B87A14, 0x7BB12BAE, 0x0CB61B38,
                0x92D28E9B, 0xE5D5BE0D, 0x7CDCEFB7, 0x0BDBDF21, 0x86D3D2D4, 0xF1D4E242,
                0x68DDB3F8, 0x1FDA836E, 0x81BE16CD, 0xF6B9265B, 0x6FB077E1, 0x18B74777,
                0x88085AE6, 0xFF0F6A70, 0x66063BCA, 0x11010B5C, 0x8F659EFF, 0xF862AE69,
                0x616BFFD3, 0x166CCF45, 0xA00AE278, 0xD70DD2EE, 0x4E048354, 0x3903B3C2,
                0xA7672661, 0xD06016F7, 0x4969474D, 0x3E6E77DB, 0xAED16A4A, 0xD9D65ADC,
                0x40DF0B66, 0x37D83BF0, 0xA9BCAE53, 0xDEBB9EC5, 0x47B2CF7F, 0x30B5FFE9,
                0xBDBDF21C, 0xCABAC28A, 0x53B39330, 0x24B4A3A6, 0xBAD03605, 0xCDD70693,
                0x54DE5729, 0x23D967BF, 0xB3667A2E, 0xC4614AB8, 0x5D681B02, 0x2A6F2B94,
                0xB40BBE37, 0xC30C8EA1, 0x5A05DF1B, 0x2D02EF8D
            };
            unchecked
            {
                uint crc = (uint)(((uint)0) ^ (-1));
                var len = data.Length;
                for (var i = 0; i < len; i++)
                {
                    crc = (crc >> 8) ^ table[(crc ^ data[i]) & 0xFF];
                }
                crc = (uint)(crc ^ (-1));
                if (crc < 0)
                {
                    crc += (uint)4294967296;
                }
                byte[] result = BitConverter.GetBytes(crc);
                if (BitConverter.IsLittleEndian)
                    Array.Reverse(result);
                return result;
            }
        }

        static void GenerateLIC(string LICPath)
        {
            byte[] data = new Byte[0x900];
            byte[] magic = { 0x50, 0x53, 0x33, 0x4C, 0x49, 0x43, 0x44, 0x41,
                0x00, 0x00, 0x00, 0x01, 0x80, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x09, 0x00, 0x00, 0x00, 0x08, 0x00,
                0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x01 };
            int i = -1;
            foreach (byte single in magic)
                data[++i] = single;
            i = 0x1F;
            while (i < 0x8FF)
                data[++i] = 0;
            i = 0x800;
            data[i] = 1;
            char[] characters = G.ID.ToCharArray();
            foreach (char single in characters)
                data[++i] = (byte)single;
            byte[] crc = Crc32(data);
            i = -1;
            foreach (byte single in crc)
                data[0x20 + (++i)] = single;
            byte[] padding = new Byte[0x10000 - 0x900];
            for (i = 0; i < padding.Length; ++i)
                padding[i] = 0;
            FileStream LIC = new FileStream(LICPath, FileMode.CreateNew, FileAccess.Write, FileShare.ReadWrite);
            BinaryWriter bLIC = new BinaryWriter(LIC);
            bLIC.Write(data);
            bLIC.Write(padding);
            bLIC.Close();
        }

        static void Updates()
        {
            try
            {
                G.xmlDoc.LoadXml(G.wc.DownloadString(new Uri("https://a0.ww.np.dl.playstation.net/tpl/np/" + G.ID + "/" + G.ID + "-ver.xml")));
            }
            catch (Exception)
            {
                G.Exit("There was an error while fetching patch data.\nIf you have a working internet connection that likely means that the game you\ntried to hack is not compatible.");
            }
        }

        static void GetPatches()
        {
            Console.WriteLine($"{G.patchURLs.Count} patches were found for {G.gameName}.\nDownloading:");
            while (G.patchURLs.Count > 0)
            {
                string url = G.patchURLs.Dequeue(),
                    fname = url.Substring(url.LastIndexOf("/", StringComparison.Ordinal) + 1),
                    path = G.patchPath + "\\" + fname,
                    part = G.patchPath + "\\partial";
                bool exists = File.Exists(path);
                if (File.Exists(part)) File.Delete(part);
                try
                {
                    Console.Write(fname + " ...");
                    if ((exists && new FileInfo(path).Length == 0) || !exists) G.wc.DownloadFile(url, part);
                    if (File.Exists(part)) File.Move(part, path);
                    G.patchFNames.Enqueue(fname);
                    Console.Write(" done");
                }
                catch (WebException)
                {
                    if (File.Exists(part)) File.Delete(part);
                    Console.Write(" failed");
                    ++G.FailedPatches;
                }
                Console.Write("\n");
            }
            if (G.FailedPatches > 0)
            {
                G.Exit("Not all patches were downloaded, please try again");
            }
        }

        static void ProcessPatches()
        {
            Console.WriteLine("\nProcessing PKGs:");
            if (!Directory.Exists(G.outputDir))
                Directory.CreateDirectory(G.outputDir);
            foreach (string fname in G.patchFNames)
            {
                string path = $"{G.patchPath}\\{fname}";
                Console.Write("Decrypting " + fname + " ...");
                try
                {
                    PS3.PKGDecrypt.DecryptPKGFile(path);
                    Console.Write(" done");
                }
                catch (Exception ex)
                {
                    Console.Write(" failed\n");
                    G.Exit("Error:\n" + ex.Message);
                }
                Console.Write("\n");
                Console.Write("Extracting " + fname + " ...");
                try
                {
                    PS3.PKGExtract.ExtractFiles(path);
                    Console.Write(" done");
                }
                catch (Exception ex)
                {
                    Console.Write(" failed\n");
                    G.Exit("Error:\n" + ex.Message);
                }
                Console.Write("\n");
            }
        }

        static void ProcessParam(string ParamPath)
        {
            var B = SeekOrigin.Begin;
            var ParamStream = new FileStream(ParamPath, FileMode.Open, FileAccess.Read, FileShare.Read);
            var bParam = new BinaryReader(ParamStream);
            var paramDict = new Dictionary<String, KeyValuePair<int, int>>();
            ParamStream.Seek(0x00, B);
            byte[] paramMagic = { 0x00, 0x50, 0x53, 0x46, 0x01, 0x01, 0x00, 0x00 };
            if (!((IStructuralEquatable)paramMagic).Equals(bParam.ReadBytes(8), StructuralComparisons.StructuralEqualityComparer))
                G.Exit("Invalid PARAM.SFO");
            bool lilEndian = BitConverter.IsLittleEndian;

            ParamStream.Seek(0x08, B);
            byte[] header_0 = bParam.ReadBytes(4);
            if (!lilEndian) Array.Reverse(header_0);
            UInt32 keyTableStart = BitConverter.ToUInt32(header_0, 0);

            ParamStream.Seek(0x0C, B);
            byte[] header_1 = bParam.ReadBytes(4);
            if (!lilEndian) Array.Reverse(header_1);
            UInt32 dataTableStart = BitConverter.ToUInt32(header_1, 0);

            ParamStream.Seek(0x10, B);
            byte[] header_2 = bParam.ReadBytes(4);
            if (!lilEndian) Array.Reverse(header_2);
            UInt32 tablesEntries = BitConverter.ToUInt32(header_2, 0);

            ParamStream.Seek((int)keyTableStart, B);
            byte[] parameter_block_raw = bParam.ReadBytes((int)dataTableStart - (int)keyTableStart);
            StringBuilder parameter_block_string = new StringBuilder();
            foreach (byte character in parameter_block_raw) parameter_block_string.Append((char)character);
            string[] Parameters = parameter_block_string.ToString().Split((char)0);
            int offset = 0x14;
            for (int i = 0; i < (int)tablesEntries; i++)
            {
                ParamStream.Seek(offset, B);
                offset += 0x10;
                byte[] key = bParam.ReadBytes(0x10);
                if (key[2] != 0x04 || key[3] != 0x02) continue;
                byte[] data_len = { key[4], key[5], key[6], key[7] },
                    data_offset_rel = { key[12], key[13], key[14], key[15] };
                if (!lilEndian)
                {
                    Array.Reverse(data_len);
                    Array.Reverse(data_offset_rel);
                }
                UInt32 dataLen = BitConverter.ToUInt32(data_len, 0);
                UInt32 dataOffsetRel = BitConverter.ToUInt32(data_offset_rel, 0);
                paramDict.Add(Parameters[i], new KeyValuePair<int, int>((int)dataOffsetRel + (int)dataTableStart, (int)dataLen));
            }
            if (!paramDict.ContainsKey("TITLE") || !paramDict.ContainsKey("APP_VER"))
                G.Exit("Error while parsing PARAM.SFO\nTITLE and APP_VER categories are missing.");
            KeyValuePair<int, int> TitleID = paramDict["TITLE_ID"];
            ParamStream.Seek(TitleID.Key, B);
            G.input = new String(bParam.ReadChars(TitleID.Value)).Substring(0, 9);
            G.verOffset = paramDict["APP_VER"];
            bParam.Close();
        }

        static void ProcessGameFiles(string LICPath)
        {
            Console.WriteLine("\nProcessing game files:");
            if (!Directory.Exists(G.targetDir))
                Directory.CreateDirectory(G.targetDir);
            string source = $"{G.currentDir}\\PS3_GAME\\";
            Console.Write("  Creating directory structure ...");
            try
            {
                foreach (string dirToCreate in Directory.GetDirectories(source, "*", SearchOption.AllDirectories))
                {
                    string split = dirToCreate.Replace(source, "");
                    string realPath = G.targetDir + "\\" + split;
                    if (!Directory.Exists(realPath))
                        Directory.CreateDirectory(realPath);
                }
                Console.Write("done\n");
            }
            catch (Exception e)
            {
                Console.Write("failed\n");
                G.Exit("Error:\n" + e.Message);
            }
            string[] everyFile = Directory.GetFiles(source, "*.*", SearchOption.AllDirectories);
            var O = StringComparison.Ordinal;
            Console.Write("  Moving content ...");
            try
            {
                for (int i = 0; i < everyFile.Length; ++i)
                {
                    string split = everyFile[i].Replace(source, "");
                    if (split.IndexOf("TROPDIR\\", O) == 0
                        || (split.IndexOf("\\", O) > -1
                            && split.IndexOf("USRDIR\\", O) == 0
                            && split.LastIndexOf(".sdat", O) == split.Length - 5)
                        || split.IndexOf("\\", O) == -1
                    )
                    {
                        string dest = G.targetDir + "\\" + split;
                        if (File.Exists(dest))
                            File.Delete(dest);
                        File.Move(everyFile[i], dest);
                        everyFile[i] = null;
                    }
                }
                string eboot = G.targetDir + "\\USRDIR\\EBOOT.BIN";
                if (File.Exists(eboot))
                    File.Delete(eboot);
                File.Copy($@"{G.outputDir}{G.ID}\USRDIR\EBOOT.BIN", eboot);
                Console.Write("done\n");
            }
            catch (Exception e)
            {
                Console.Write("failed\n");
                G.Exit("Error:\n" + e.Message);
            }
            Console.Write("  Patching PARAM.SFO ...");
            try
            {
                var ParamStream = new FileStream(G.targetDir + "\\PARAM.SFO", FileMode.Open, FileAccess.Write, FileShare.Read);
                var bStream = new BinaryWriter(ParamStream);
                var version = G.newVer.ToCharArray();
                ParamStream.Seek(G.verOffset.Key, SeekOrigin.Begin);
                bStream.Write(version);
                bStream.Close();
                Console.Write("done\n");
            }
            catch (Exception e)
            {
                Console.Write("failed\n");
                G.Exit("Error:\n" + e.Message);
            }
            Console.Write("  Running make_npdata ...");
            try
            {
                using (Process p = new Process())
                {
                    p.StartInfo.FileName = G.makeNpdata;
                    p.StartInfo.UseShellExecute = false;
                    p.StartInfo.RedirectStandardOutput = false;
                    p.StartInfo.CreateNoWindow = true;
                    p.StartInfo.WorkingDirectory = G.currentDir;
                    foreach (string toConvert in everyFile)
                    {
                        if (toConvert == null
                            || toConvert.Replace(source, "").IndexOf("EBOOT.BIN", O) != -1
                            || toConvert.Replace(source, "").IndexOf("LIC.DAT", O) != -1)
                        {
                            continue;
                        }
                        string dest = G.targetDir + "\\" + toConvert.Replace(source, "");
                        p.StartInfo.Arguments = "-e \"" + toConvert + "\" \"" + dest + "\" 0 1 3 0 16";
                        p.Start();
                        p.WaitForExit();
                        if (File.Exists(dest))
                            File.Delete(dest);
                    }
                    p.StartInfo.Arguments = "-e \"" + LICPath + "\" \"" + G.targetDir +
                        "\\LICDIR\\LIC.EDAT\" 1 1 3 0 16 3 00 EP9000-" + G.newID
                        + "_00-0000000000000001 1";
                    p.Start();
                    p.WaitForExit();
                }
                Console.Write("done\n");
            }
            catch (Exception e)
            {
                Console.Write("failed\n");
                G.Exit("Error:\n" + e.Message);
            }
            Console.Write("  Deleting source folder ...");
            try
            {
                Directory.Delete(source, true);
                Console.Write("done\n");
            }
            catch (Exception e)
            {
                Console.Write("failed\n");
                G.Exit("Error:\n" + e.Message);
            }
        }

        [STAThread]
        static void Main(string[] args)
        {
            if (!File.Exists(G.makeNpdata))
                G.Exit("Missing make_npdata.exe");
            string ParamPath = G.currentDir + @"\PS3_GAME\PARAM.SFO",
                LICPath = G.currentDir + @"\PS3_GAME\LICDIR\LIC.DAT";
            bool ParamExists = File.Exists(ParamPath);
            bool LICExists = File.Exists(LICPath);
            bool exitAfterPatch = false;
            string HelpMsg = "To convert a game, please place the PS3_GAME folder next to this program and run it with no arguments.\n\n" +
                "To check for compatibility, use the game's ID as an argument like so:\n" +
                "   \"CFW2OFW Helper.exe\" BLUS01234";
            Console.WriteLine(" --- CFW2OFW Helper v1 ---\nThanks to mathieulh for PKG related code!\n");
            switch (args.Length)
            {
            case 0:
                if (ParamExists)
                {
                    try
                    {
                        ProcessParam(ParamPath);
                    }
                    catch (Exception ex)
                    {
                        G.Exit("An error occured while trying to read PARAM.SFO:\n" + ex.Message);
                    }
                }
                else
                {
                    G.Exit(HelpMsg);
                }
                break;
            case 1:
                switch (args[0])
                {
                case "help":
                case "-help":
                case "--help":
                case "/?":
                case "-h":
                    G.Exit(HelpMsg);
                    break;
                default:
                    G.input = args[0];
                    exitAfterPatch = true;
                    break;
                }
                break;
            default:
                G.Exit("Too many arguments!");
                break;
            }
            string pattern = @"^B[LC][JUEAK][SM]\d{5}$";
            if (!new Regex(pattern, RegexOptions.Compiled).IsMatch(G.input))
                G.Exit("Invalid game ID: " + args[0]);
            else
                G.ID = G.input;

            string lowID = G.ID.Substring(0, 4),
                highID = G.ID.Substring(4);

            /// http://www.ps3hax.net/showthread.php?t=71364&p=742374&viewfull=1#post742374
            switch (lowID)
            {
            case "BLJS":
            case "BLJM":
                lowID = "NPJB";
                break;
            case "BCJS":
                lowID = "NPJA";
                break;
            case "BLUS":
                lowID = "NPUB";
                break;
            case "BCUS":
                lowID = "NPUA";
                break;
            case "BLES":
                lowID = "NPEB";
                break;
            case "BCES":
                lowID = "NPEA";
                break;
            case "BLAS":
            case "BLKS":
                lowID = "NPHB";
                break;
            case "BCAS":
            case "BCKS":
                lowID = "NPHA";
                break;
            default:
                G.Exit("This region is not supported for this hack: " + lowID);
                break;
            }
            G.newID = lowID + highID;
            Console.WriteLine("Game identified: " + G.ID);
            if (!exitAfterPatch)
                Console.WriteLine("Target ID: " + G.newID);
            Console.Write("\n");
            ServicePointManager.ServerCertificateValidationCallback += delegate { return true; };
            WebRequest.DefaultWebProxy = null;
            G.wc.Proxy = null;
            Updates();
            XmlNodeList patch = G.xmlDoc.GetElementsByTagName("package");
            if (patch.Count > 0)
            {
                
                G.gameName = new Regex(@"[^A-Za-z0-9 _]", RegexOptions.Compiled).Replace(G.xmlDoc.GetElementsByTagName("TITLE").Item(0).InnerText, "");
                G.outputDir = $@"{G.currentDir}\{G.gameName} ({G.ID})\";
                G.targetDir = G.outputDir + G.newID;
                if (exitAfterPatch)
                    G.Exit(G.gameName + " [" + G.ID + "] seems to be compatible.");
                foreach (XmlNode package in patch)
                {
                    XmlAttribute url = package.Attributes["url"];
                    if (url != null)
                    {
                        G.patchURLs.Enqueue(url.Value);
                    }
                }
                G.newVer = patch[patch.Count - 1].Attributes["version"].Value;
            }
            else
                G.Exit("No patches found.\n" + G.ID + " is not compatible with this hack.\n");
            if (!Directory.Exists(G.patchPath))
                Directory.CreateDirectory(G.patchPath);
            if (!LICExists)
            {
                Directory.CreateDirectory(G.currentDir + @"\PS3_GAME\LICDIR");
                Console.Write("LIC.DAT is missing.\nGenerating LIC.DAT ...");
                try
                {
                    GenerateLIC(LICPath);
                    Console.Write(" done\n");
                }
                catch (Exception)
                {
                    Console.Write(" failed");
                    G.Exit("");
                }
            }
            GetPatches();
            ProcessPatches();
            ProcessGameFiles(LICPath);
            Console.Write("\nDone.\nPress any key to exit . . .");
            Console.ReadKey(false);
        }
    }
}