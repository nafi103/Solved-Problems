#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e5
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

void solve()
{
    string st,en;
    cin>>st>>en;
    vector<vector<vector<bool>>>visited(26,vector<vector<bool>>(26,vector<bool>(26,0)));
    int m;
    cin>>m;
    while(m--){
        vector<string>tmp(3);
        readv(tmp);
        for(auto &x: tmp[0]){
            for(auto &y: tmp[1]){
                for(auto &z: tmp[2]){
                    visited[x-'a'][y-'a'][z-'a'] = true;
                }
            }
        }
    }
    int a = st[0]-'a', b = st[1]-'a', c = st[2] - 'a', ans = -1;
    int x[] = {1,-1,0,0,0,0};
    int y[] = {0,0,1,-1,0,0};
    int z[] = {0,0,0,0,1,-1};
    using arr = array<int,4>;
    queue<arr>pq;
    pq.push({0,a,b,c});
    while(!pq.empty()){
        auto [d,f,s,t] = pq.front();
        pq.pop();
        if(visited[f][s][t])
            continue;
        if(f==en[0]-'a' and s==en[1]-'a' and t==en[2]-'a'){
            ans = d;
            break;
        }
        visited[f][s][t] = true;
        for(int i = 0; i<6; i++){
            int nf = (f+x[i]+26)%26, ns = (s+y[i]+26)%26, nt = (t+z[i]+26)%26;
            if(!visited[nf][ns][nt]){
                pq.push({d+1,nf,ns,nt});
            }
        }
    }
    cout<<ans<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        cout<<"Case "<<z<<": ";
        solve();
    }
}