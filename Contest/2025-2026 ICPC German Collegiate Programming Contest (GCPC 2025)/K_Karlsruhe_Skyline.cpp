#include<bits/stdc++.h>
using namespace std;
 #define int long long
 void solve(){
    int n,a,b;
    cin>>n>>a>>b;
    if(a+b-1>n or (a==1 and b==1 and n>1)){
        cout<<"no"<<endl;
    }else{
        cout<<"yes"<<endl;
        bool flag = false;
        if(a>b){
            swap(a,b);
            flag = true;
        }
        vector<int>perm(n,-1);
        perm[a-1] = n;
        int i = 1, k = n-b+1;
        for(i; i<a; i++){
            perm[i-1] = i;
        }
        for(int j = n-1; k<n; j--, k++){
            perm[j] = k;
        }
        for(int id = 0; id<n; id++){
            if(perm[id]==-1){
                perm[id] = i++;
            }
        }
        if(flag)
            reverse(perm.begin(),perm.end());
        for(auto &x: perm){
            cout<<x<<" ";
        }
        cout<<endl;
    }
}
 int32_t main(){
    ios::sync_with_stdio(false),cin.tie(nullptr),cout.tie(nullptr);
    int t = 1;
    for(int z = 1; z<=t; z++){
        //cout<<"Case "<<z<<": ";
        solve();
    }
    return 0;
}