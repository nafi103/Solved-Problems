#include<bits/stdc++.h>
using namespace std;
 int main(){
    int t;
    cin>>t;
    while(t--){
        int n, i =0,cnt = 0;
        bool flag = true;
        string str;
        cin>>n>>str;
        while(i<n){
            if(str[i]=='Q') cnt++;
            else cnt--;
            if(cnt<0)   cnt=0;
            i++;
        }
        if(!cnt)    cout<<"Yes" << endl;
        else cout<<"No" << endl;
    }
}