#include <bits/stdc++.h>
using namespace std;
 int main()
{
    int t;
    cin >> t;
    while (t--)
    {
        int n;
        char a;
        cin >> n;
        string str;
        bool flag = true;
        cin >> str;
        if (n < 4)
            flag = false;
        else
        {
            transform(str.begin(), str.end(), str.begin(), ::tolower);
            for (int i = 1; i < str.size(); i++)
            {
                if (str[i] == str[i - 1])
                {
                    str.erase(str.begin() + i);
                    i--;
                }
            }
            if(!(str=="meow"))  flag = false;
        }
        if(flag)    cout<<"YES"<<endl;
        else cout<<"NO"<<endl;
    }
}
