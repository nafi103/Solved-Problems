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


void solve()
{
    int n,m,k,in_water = 0;
    cin>>n>>m>>k;
    string str;
    cin>>str;
    int curr = -1;
    while(curr<n){
        if(in_water>k or str[curr]=='C'){
            no;
            return;
        }
        if(curr>=0 and str[curr]=='W'){
            curr++;
            in_water++;
            continue;
        }
        if(curr+m>=n){
            curr = n;
            break;
        }
        bool flag = true;
        int pos = -1;
        for(int i = curr+1; i<=curr+m; i++){
            if(str[i]=='L'){
                pos = i;
                flag = false;
            }
            else if(str[i]=='W' and flag){
                pos = i;
            }
        }
        if(flag and pos==-1){
            no;
            return;
        }
        curr = pos;
    }
    if(in_water<=k)
        yes;
    else no;
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