#include <bits/stdc++.h>
using namespace std;
 void solve(string* s)
{
    string str;
    int n;
    cin >> n >> str;
    if(s->find(str)!=string::npos)  cout<<"YES"<<endl;
    else cout<<"NO"<<endl;
}
 int main()
{
    string s = "";
    for (int i = 1; s.size()<=16; i++)
    {
        if(i%3==0)  s.push_back('F');
        if(i%5==0) s.push_back('B');
    }
    int t;
    cin >> t;
    while (t--)
        solve(&s);
}