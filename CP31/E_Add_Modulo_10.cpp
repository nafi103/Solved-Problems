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
#define yes cout<<"Yes"<<endl
#define no cout<<"No"<<endl
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

bool all_same(vector<int>&v, int &n){
    for(int i = 1; i<n; i++){
        if(v[i]!=v[i-1]) return false;
    }
    return true;
}

int rem(int n){
    return n%10;
}


void solve()
{
    int n;
    cin>>n;
    vector<int>v(n);
    readv(v);
    bool edge = false;
    for(int i = 0; i<n; i++){
        if(v[i]%10==5 or v[i]%10==0){
            if(v[i]%10==5) v[i]+=5;
            edge = true;
        }
        if(rem(v[i])&1) v[i]+=rem(v[i]);
    }
    if(all_same(v,n)){
        yes;
        return;
    }else if(edge){
        no;
        return;
    }
    sort(all(v));
    for(int i = 0; i<n-1; i++){
        while(rem(v[i]) != rem(v[i+1])){
            v[i]+=(rem(v[i]));
        }
        int dis = v[i+1]-v[i];
        if((dis/10)&1){
            no;
            return;
        }
    }
    yes;
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