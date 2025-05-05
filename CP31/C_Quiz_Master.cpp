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
#define inf 1e18+10
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

const int N = 1e5 + 10;
vector<vector<int>>divisors(N,{1});


void solve()
{
    int n,m,ans = INT_MAX;
    cin>>n>>m;
    vector<int>v(n);
    readv(v);
    sort(all(v));
    map<int,int>mp;
    for(int i = 0,j = 0; i<n; i++){
        while(j<n and sz(mp)<m){
            for(auto &x: divisors[v[j]]){
                if(x>m)
                    break;
                mp[x]++;
            }
            j++;
        }
        if(sz(mp)==m){
            ans = min(ans,v[j-1]-v[i]);
        }else{
            break;
        }
        vector<int>rmv;
        for(auto &x: divisors[v[i]]){
            if(x>m)
                break;
            mp[x]--;
            if(mp[x]==0)
                rmv.push_back(x);
        }
        for(auto &x: rmv)
            mp.erase(x);
    }
    cout<<(ans==INT_MAX?-1:ans)<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    for(int i = 2; i<N; i++){
        for(int j = i; j<N; j+=i){
            divisors[j].push_back(i);
        }
    }
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}