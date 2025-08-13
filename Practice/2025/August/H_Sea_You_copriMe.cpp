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
const int N = 1e6+10;
vector<int>spf(N);

void solve()
{
    int n,m;
    cin>>n>>m;
    vector<int>v(n);
    readv(v);
    vector<int>cnt(m+1,0);
    for(int i = 0; i<n; i++){
        int x = v[i], new_num = 1;
        vector<int>prime_factors;
        while(x>1){
            int y = spf[x];
            new_num*=y;
            prime_factors.push_back(y);
            while(x%y==0)
                x/=y;
        }
        v[i] = new_num;
        int r = 1<<sz(prime_factors);
        for(int mask = 1; mask<r; mask++){
            int num = 1;
            for(int j = 0; j<sz(prime_factors); j++){
                if(mask&(1<<j))
                    num*=prime_factors[j];
            }
            cnt[num]++;
        }
    }
    vector<pair<int,int>>last(n);
    for(int i = 0; i<n; i++){
        int not_coprimes = 0, x = v[i];
        vector<int>prime_factors;
        while(x>1){
            int y = spf[x];
            prime_factors.push_back(y);
            while(x%y==0)
                x/=y;
        }
        int r = 1<<sz(prime_factors);
        for(int mask = 1; mask<r; mask++){
            int num = 1;
            for(int j = 0; j<sz(prime_factors); j++){
                if(mask&(1<<j))
                    num*=prime_factors[j];
            }
            if(__builtin_popcount(mask) & 1){
                not_coprimes+=cnt[num];
            }else{
                not_coprimes-=cnt[num];
            }
        }
        last[i] = {n-max(not_coprimes,1ll),i};
    }
    sort(all(last));
    if(last[n-1].ff==0){
        cout<<0<<endl;
        return;
    }
    vector<int>ans;
    int y = v[last[n-1].ss], x;
    for(x = 0; x<n; x++){
        if(gcd(y,v[last[x].ss])==1){
            break;
        }
    }
    int tx = x;
    ans.push_back(last[n-1].ss);
    ans.push_back(last[x].ss);
    x = v[last[x].ss];
    for(int i = 0; i<n; i++){
        int z = v[last[i].ss];
        if(gcd(x,z)==1)
            last[i].ff--;
        if(gcd(z,y)==1)
            last[i].ff--;
    }
    last.pop_back();
    last.erase(last.begin()+tx);
    n-=2;
    sort(all(last));
    if(last[n-1].ff==0){
        cout<<0<<endl;
        return;
    }
    y = v[last[n-1].ss];
    for(x = 0; x<n; x++){
        if(gcd(y,v[last[x].ss])==1){
            break;
        }
    }
    ans.push_back(last[n-1].ss);
    ans.push_back(last[x].ss);
    for(auto &p: ans)
        cout<<p+1<<" ";
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
    for(int i = 0; i<N; i++)
        spf[i] = i;
    for(int i = 2; i*i<N; i++){
        if(spf[i]==i){
            for(int j = i+i; j<N; j+=i){
                spf[j] = min(spf[j],i);
            }
        }
    }
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}