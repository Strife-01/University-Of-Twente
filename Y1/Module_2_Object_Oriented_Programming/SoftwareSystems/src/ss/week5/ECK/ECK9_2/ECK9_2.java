package ss.week5.ECK.ECK9_2;

import java.io.*;

public class ECK9_2 {
    Reader reader;
    Writer writer;

    public ECK9_2(String fileInputPath, String fileOutputPath) throws IOException {
        reader = new FileReader(fileInputPath);
        writer = new FileWriter(fileOutputPath, true);
    }

    public void insertData() throws IOException {
        int c;
        String data = "";
        while ((c = reader.read()) != -1) {
            if (Character.isAlphabetic(c)) {
                data = data.concat(Character.toString(c));
            } else {
                if (!data.isEmpty()) {
                    SortTreeDemo.treeInsert(data);
                }
                data = "";
            }
        }
        if (!data.isEmpty()) {
            SortTreeDemo.treeInsert(data);
        }
    }

    private void fileInsert(SortTreeDemo.TreeNode node) {
        if ( node != null ) {
            fileInsert(node.left);
            try {
                ((FileWriter) writer).write(node.item + "\n");
                writer.flush();
            } catch (IOException e) {
                System.out.println(e.getMessage());
            }
            fileInsert(node.right);
        }
    }

    public static void main(String[] args) {
        try {
            ECK9_2 obj = new ECK9_2("src/ss/week5/ECK/ECK9_2/infile","src/ss/week5/ECK/ECK9_2/outfile");
            obj.insertData();
            obj.fileInsert(SortTreeDemo.root);
        } catch (IOException e) {
            System.out.println(e.getMessage());
        }
    }
}
