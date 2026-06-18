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

int find_mex(vector<int>&mp){
    int mex = 0;
    for(auto &s: mp){
        if(s>0)
            mex++;
        else
            break;
    }
    return mex;
}

void solve()
{
    int n,mex = 0;
    cin>>n;
    vector<int>v(n),ans;
    vector<int>mp(n+1,0);
    for(int i = 0; i<n; i++){
        cin>>v[i];
        mp[v[i]]++;
    }
    mex = find_mex(mp);
    for(int i = 0; i<n; i++){
        if(v[i]!=i){
            ans.push_back(i);
            mp[v[i]]--;
            v[i] = mex;
            mp[mex]++;
            mex = find_mex(mp);
            while(mex<n){
                ans.push_back(mex);
                mp[v[mex]]--;
                v[mex] = mex;
                mp[mex]++;
                mex = find_mex(mp);
            }
        }
    }
    cout<<sz(ans)<<endl;
    for(auto &x:  ans){
        cout<<x+1<<" ";
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
    cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}