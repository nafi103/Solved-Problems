#include<bits/stdc++.h>
using namespace std;
 #define int long long
 vector<vector<int>>g;
 void dfs(int node, vector<bool>&visited){
    visited[node] = true;
    for(auto &nbr: g[node]){
        if(!visited[nbr]){
            dfs(nbr,visited);
        }
    }
}
 int32_t main(){
    int n,m;
    cin>>n>>m;
    g.resize(n+1);
    vector<bool>a(n+1,false), b(n+1,false);
    for(int i = 0; i<m; i++){
        int u,v;
        cin>>u>>v;
        g[u].push_back(v);
    }
    int x,y;
    cin>>x>>y;
    dfs(x,a);
    dfs(y,b);
    int s = -1;
    for(int i = 1; i<=n; i++){
        if(a[i] and b[i]){
            s = i;
            break;
        }
    }
    if(s==-1){
        cout<<"no"<<endl;
    }else{
        cout<<"yes"<<endl;
        cout<<s<<endl;
    }
    return 0;
}