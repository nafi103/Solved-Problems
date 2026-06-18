#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
#define mod 998244353
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcount(x)
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
template <class T> using pbds = tree<T, null_type, less_equal<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/


void solve()
{
    int n; cin>>n;
    string str;
    vector<int>v(n),pos(n+1),jump(n,-1);
    for(int i = 0;  i<n; i++){
        cin>>v[i];
        pos[v[i]] = i;
    }
    jump[pos[n]] = 0;
    for(int i = n-1, idx = pos[i]; i>=1; i--,idx = pos[i]){
        jump[idx] = 0;
        for(int j = idx+i; j<n; j+=i){
            if(jump[j]==-1) continue;
            if(!jump[j]){
                jump[idx] = 1;
                break;
            }
        }
        for(int j = idx-i; j>=0; j-=i){
            if(jump[j]==-1) continue;
            if(!jump[j]){
                jump[idx] = 1;
                break;
            }
        }
    }
    for(int i = 0; i<n; i++){
        if(jump[i]) cout<<'A';
        else cout<<'B';
    }
    cout<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}