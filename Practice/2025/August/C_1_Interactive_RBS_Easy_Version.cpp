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
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
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
    int n,valid, o , c;
    cin>>n;
    cout<<"? "<<n;
    for(int i = 1; i<=n; i++){
        cout<<" "<<i;
    }
    cout<<endl;
    cin>>valid;
    if(valid){
        int l = 1, r = n;
        while(r-l>1){
            int mid = (l+r)/2;
            cout<<"? "<<mid-l+1;
            for(int i = l; i<=mid; i++){
                cout<<" "<<i;
            }
            cout<<endl;
            cin>>valid;
            if(valid)
                r = mid;
            else
                l = mid;
        }
        o = l, c = r;
    }else{
        o = n, c = 1;
    }
    vector<char>ans(n+1);
    ans[o] = '(';
    ans[c] = ')';
    vector<int>rem;
    rem.reserve(n-2);
    for(int i = 1; i<=n; i++){
        if(i!=o and i!=c){
            rem.push_back(i);
        }
    }
    while(sz(rem)){
        if(sz(rem)==1){
            cout<<"? "<<2<<" "<<o<<" "<<rem[0]<<endl;
            cin>>valid;
            if(valid)
                ans[rem[0]] = ')';
            else
                ans[rem[0]] = '(';
            rem.pop_back();
        }else{
            cout<<"? 7";
            int x = rem[sz(rem)-1], y = rem[sz(rem)-2];
            for(int i = 0; i<3; i++){
                cout<<" "<<x<<" "<<y;
                if(i==0)
                    cout<<" "<<c;
            }
            cout<<endl;
            cin>>valid;
            if(valid==0){
                ans[x] = ')';
                ans[y] = ')';
            }else if(valid==2){
                ans[x] = ')';
                ans[y] = '(';
            }else if(valid==1){
                ans[x] = '(';
                ans[y] = '(';
            }else{
                ans[x] = '(';
                ans[y] = ')';
            }
            rem.pop_back();
            rem.pop_back();
        }
    }
    cout<<"! ";
    for(int i = 1; i<=n; i++)
        cout<<ans[i];
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}