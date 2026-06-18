#include <bits/stdc++.h>
#define ll long long
using namespace std;

int main(){
    ll cnt = 1, mxcnt = 1;
    string str;
    cin>>str;
    for (int i = 1; i < (int)str.size(); i++)
    {
        if(str[i]==str[i-1]) cnt++;
        else{
            mxcnt = max(mxcnt,cnt);
            cnt = 1;
        }
    }
    mxcnt = max(mxcnt,cnt);
    cout<<mxcnt<<endl;
}