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

int query(vector<int>&a, int n){
    cout<<"? "<<n;
    for(int i = 0; i<n; i++){
        cout<<" "<<a[i];
    }
    cout<<endl;
    int q;
    cin>>q;
    return q;
}

int query(vector<int>&a){
    cout<<"? "<<sz(a);
    for(int i = 0; i<sz(a); i++){
        cout<<" "<<a[i];
    }
    cout<<endl;
    int q;
    cin>>q;
    return q;
}

void solve()
{
    int n,valid, o , c;
    cin>>n;
    vector<int>a(n);
    vector<char>ans(n+1);
    iota(a.begin(),a.begin()+n,1);
    valid = query(a,n);
    if(valid){
        int l = 1, r = n;
        while(r-l>1){
            int mid = (l+r)/2, m = mid-l+1;
            iota(a.begin(),a.begin()+m,l);
            valid = query(a,m);
            if(valid)
                r = mid;
            else
                l = mid;
        }
        o = l, c = r;
    }else{
        o = n, c = 1;
    }
    a.clear();
    for(int i = 7; i>=0; i--){
        for(int j = (1<<i); j>0; j--){
            a.push_back(o);
            a.push_back(c);
        }
        a.push_back(c);
    }
    int f0 = query(a);
    for(int i = 1; i<=n; i+=8){
        a.clear();
        for(int j = i, segment = 128; j<i+8; j++, segment>>=1){
            a.push_back((j<=n? j:o));
            a.push_back(c);
            for(int k = 1; k<=segment-1; k++){
                a.push_back(o);
                a.push_back(c);
            }
            a.push_back(c);
        }
        int f1 = query(a);
        int diff = f0-f1;
        for(int j = i, p = 7; j<i+8 and j<=n; j++,p--){
            if((diff&(1<<p)))
                ans[j] = ')';
            else
                ans[j] = '(';
        }
    }
    cout<<"! ";
    for(int i = 1; i<=n; i++){
        cout<<ans[i];
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}