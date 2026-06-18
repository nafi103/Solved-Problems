#include<bits/stdc++.h>
using namespace std;
 void solution()
{
    int n;
    string str;
    cin>>n>>str;
    int ans = -1;
    for(int i=0; i<n-1; i++){
        if(str[i]=='R' && str[i+1]=='L'){
            ans = 0;
            break;
        }else if(str[i]=='L' && str[i+1]=='R'){
            ans = i+1;
        }
    }
    cout<<ans<<endl;
}
 int main(){
    int t;
    cin>>t;
    while(t--)  solution();
}