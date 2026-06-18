#include <bits/stdc++.h>
using namespace std;
 int main()
{
    int t;
    cin >> t;
    while (t--)
    {
        int k = 3, flag = 1;
        string str;
        char arr[3] = {'Y', 'e', 's'};
        cin >> str;
        for (int i = 0; i < 3; i++)
        {
            {
                if (str[0] == arr[i])
                {
                    k = i;
                }
            }
        }
        if (k < 3)
        {
            for (int i = 0; i < str.size(); i++)
            {
                if (str[i] != arr[k])
                {
                    flag = 0;
                    break;
                }
                k++;
                if (k == 3)
                    k = 0;
            }
        }else{
            flag = false;
        }
        if (flag)
            cout << "YES" << endl;
        else
            cout << "NO" << endl;
    }
}