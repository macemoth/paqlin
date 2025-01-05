package com.macemoth

import java.io.File
import java.lang.Character.isAlphabetic
import kotlin.system.exitProcess

enum class Mode {
    COMPRESS, DECOMPRESS
}

const val EOF = -1

class FileHandler(file: File) {

    init {
        file.createNewFile()
    }
    val reader = file.inputStream()
    val writer = file.outputStream()


    fun writeb(content: Int) {
        writer.write(content)
    }

    fun writeLine(content: CharArray) {
        for (c in content)
            this.writeb(c.code)
    }

    fun readc(): Int {
        return reader.read()
    }

    fun readLine(): String {
        var c = reader.read()
        val result = StringBuilder()
        while (c != EOF && c >= 32)
            result.append((c).toChar())
            c = reader.read();
        if (c.toChar() == '\r')
            reader.read()
        return result.toString()
    }

    fun close() {
        writer.close()
        reader.close()
    }
}

class Encoder(archive: FileHandler, mode: Mode, predictor: Predictor) {
    var archive = archive
    var x1: ULong = 0u
    var x2: ULong = 0xffffffffu
    var x: ULong = 0u
    var x_bytes = 0
    var e_bytes = 0
    var eofs = 0
    val mode = mode
    val predictor = predictor

    fun encode(y_in: Int): Int {
        e_bytes++
        var y = y_in

        if (e_bytes == 3792)
            print("")

        var p = (predictor.p().inv() and 0xffff).toULong()
        var xdiff = x2 - x1
        var xmid = x1

        if (xdiff >= 0x10000000u)
            xmid += (xdiff shr 16) * p
        else if (xdiff >= 0x1000000u)
            xmid += ((xdiff shr 12) * p) shr 4
        else if (xdiff >= 0x100000u)
            xmid += ((xdiff shr 8) * p) shr 8
        else if (xdiff >= 0x10000u)
            xmid += ((xdiff shr 4) * p) shr 12
        else
            xmid += (xdiff * p) shr 16

        if (xmid < x1 || xmid >= x2) {
            println("Range unsplittable: x1=$x1 xmid=$xmid x2=$x2")
            exitProcess(2)
        }

        if (mode == Mode.COMPRESS) {
            if (y == 1)
                x1 = xmid + 1u
            else
                x2 = xmid
        } else {
            if (x <= xmid) {
                y = 0
                x2 = xmid
            } else {
                y = 1
                x1 = xmid + 1u
            }
        }
        predictor.update(y)

        while (((x1 xor x2) and 0xff000000u).toInt() == 0) {
            if (mode == Mode.COMPRESS) {
                archive.writeb(((x2 shr 24) and 0xffu).toInt())
                if (x_bytes > 318)
                    print("")
                 println("$e_bytes: ${(x2)}")
                x_bytes++
            }
            x1 = x1 shl 8
            x2 = (x2 shl 8) + 255u

            if (mode == Mode.DECOMPRESS) {
                var c = archive.readc()
                if (c == EOF) {
                    c = 0
                    if (++eofs > 5)
                        println("Premature end of archive")
                } else
                    x_bytes++
                x = (x shl 8) + (c  ).toUInt()
            }
        }
        return y
    }

    fun close() {
        if (mode == Mode.COMPRESS) {
            while (((x1 xor x2) and 0xff000000u) == (0u).toULong()) {
                archive.writeb((x2 shr 24).toInt())
                x1 = x1 shl 8
                x2 = (x2 shl 8) + 255u
                x_bytes++
            }
            archive.writeb(((x2 shr 24) and 0xffu).toInt())
            x_bytes++
        }
    }

    fun compress(c_in: Int) {
        var c = c_in
        for (i in 0 until 8) {
            encode(if ((c and 128) != 0) 1 else 0)
            c = c shl 1
        }
    }

    fun decompress(): Int {
        var c = 0
        for (i in 0 until 8)
            c = (c shl 1) + encode(0)
        return c
    }
}

class Predictor(val n: Int = 0x400000, val nx: Int = 6) {

    val wt = IntArray(n)
    val c0 = IntArray(n)
    val c1 = IntArray(n)
    val x = IntArray(nx)
    var s0: ULong = 1u
    var s7: ULong = 0u
    var s3: ULong = 0u
    var sw0: ULong = 0u
    var sw1: ULong = 0u
    var pr = 32768
    var sigma2 = Sigma2(rl = 0.38)
    var g = G()

    init {
        for (i in 0 until nx) {
            x[i] = 0
        }
        for (i in 0 until n) {
            c0[i] = 0
            c1[i] = 0
            wt[i] = 0
        }
    }

    fun p(): Int {
        return pr
    }

    fun update(y: Int) {
        val error = (y shl 16) - p()
        val rs = (1024 * 0.06).toInt()
        val cmax = 250
        for (i in 0 until nx) {
            val idx = x[i] + s0.toInt()
            // Increase count
            c0[idx] += 1-y
            c1[idx] += y
            // Keep counts smaller than cmax
            if ((c0[idx] > cmax) || (c1[idx] > cmax)) {
                c0[idx] = c0[idx] shr 1
                c1[idx] = c1[idx] shr 1
            }
            // Update NN weights, but concatenate c0 and c1 for sigma 2
            val c01 = ((c0[idx] and 0xff) shl 8) + (c1[idx] and 0xff)
            wt[idx] += ((error * (rs + sigma2.get(c01))).shr(16))
        }
        // Update current state from input bit y
        s0 = (s0 shl 1) or y.toULong() // Encode position and bits 0-7 of current byte
        if (s0 >= 256u) { // Check for end of byte
            if (this.isAlpha((s0 and 255u).toInt().toChar()))
                sw0 = sw0 * 997u + s0
            else {
                if (sw0 != 0u.toULong())
                    sw1 = sw0
                sw0 = 0u
            }
            s7 = (s7 shl 8) or (s3 shr 24) // Bytes 7-4 backwards
            s3 = (s3 or (s0 and 255u)) shl 8 // Last 3 full bytes, padded with 0 byte
            s0 = 1u

            // Select active inputs (x[1..4] are hashes using modulo primes < 2^22 - 2^16 - 2^8)
            x[0] = (4128768u + (s3 and 0xffffu)).toInt() // Last byte
            x[1] = ((s3 and 0xffffffu) % 4128511u).toInt()
            x[2] = (s3 % 4128493u).toInt()
            x[3] = ((s3 + s7 * 0x3000000u.toULong()) % 4128451u.toULong()).toInt()
            x[4] = ((sw1 + sw0 * 29u.toULong()) % 4128401u.toULong()).toInt()
            x[5] = (sw0 % 4128409.toULong()).toInt()
        }

        var sum = 0
        for (i in 0 until nx) {
            val idx = x[i] + s0.toInt()
            sum += wt[idx]
        }
        pr = g.get(sum).toInt()

    }

    private fun isAlpha(c: Char): Boolean {
        return (c >= 'a' && c <= 'z') ||
                (c >= 'A' && c <= 'Z') ||
                (c >= '0' && c <= '9')
    }
}

class G {

    val table = UShortArray(11265)

    init {
        // Compute every 64th point explicitly
        for (i in 0 .. 11264 step 64)
            table[i] = minOf(65535, (65536.0 / (1 + Math.exp(-i / 1024.0))).toInt()).toUInt().toUShort()
        // Interpolate in between
        for (i in 0 .. 11200 step 64)
            for (j in 1 until 64)
                table[i + j] = (table[i] + (((table[i + 64] - table[i]) * j.toUShort()) shr 6)).toUShort()
    }


    fun get(x: Int): UShort {
        return if (x >= 11265)
            65535u
        else if (x <= -11265)
            0u
        else if (x >= 0)
            table[x]
        else
            (65535u - table[-x]).toUShort()
    }
}

class Sigma2(rl: Double) {

    val table = ShortArray(65536)

    init {
        for (c0 in 0 until 256)
            for (c1 in 0 until 256)
                table[(c0 shl 8) + c1] = ((1024 * rl * (c0 + c1 + 1) / ((c0 + 0.5) * (c1 + 0.5))).toInt()).toShort()

    }

    fun get(c01: Int): Short {
        return this.table[c01 and 0xffff]
    }

}


fun main(args: Array<String>) {
    if (args.size < 1) {
        print(
            "P12 - File compressor\n" +
                    "To compress: P12 archive filename [filename...]\n" +
                    "To extract: P12 archive\n"
        )
        return
    }

    val archive = File(args[0])
    val archiveHandler = FileHandler(archive)

    if (args.size < 2) {
        println("Extracting archive ${args[0]}")
        if (archiveHandler.readLine() != "P12") {
            println("Archive file ${args[0]} is not in P12 format")
            return
        }

        val filenames = arrayListOf<String>()
        val filesizes = arrayListOf<Long>()

        while (true) {
            val line = archiveHandler.readLine()
            if (line.length > 10) {
                filesizes.add(line.substring(0, 10).toLong())
                filenames.add(line.substring(10))
            } else break
        }

        val encoder = Encoder(archiveHandler, Mode.DECOMPRESS, Predictor())
        for (i in 0 until filenames.size) {
            // Comparison with existing file left out
            val size = filesizes[i]
            // Iterate bytes
            for (j in 0 until size) {
                val c1 = encoder.decompress()
            }
        }
    } else {
        val files = arrayListOf<File>()
        for (i in 1 until args.size) {
            files.add(File(args[i]))
        }
        // Write archive header
        for (f in files) {
            archiveHandler.writeLine("P12\r\n".toCharArray())
            if (f.length() >= 0)
                archiveHandler.writeLine("%9d %s\r\n".format(f.length(), f.name).toCharArray())
        }
        archiveHandler.writeb(0x1A)
        archiveHandler.writeb('\u000C'.code)
        archiveHandler.writeb(0)

        // Write data
        val encoder = Encoder(archiveHandler, Mode.COMPRESS, Predictor())
        for (f in files) {
            if (f.length() >= 0) {
                println(f.name)
                val fileIterator = f.inputStream().readBytes().iterator()
                // Iterate bytes
                while (fileIterator.hasNext()) {
                    encoder.compress(fileIterator.next().toInt())
                }
            }
        }
        encoder.close()
        archiveHandler.close()
    }
    return
}