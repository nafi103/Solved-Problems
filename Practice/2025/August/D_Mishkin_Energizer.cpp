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
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/

char will_insert(char &a, char &b){
    if((a=='L' and b=='T') or (a=='T' and b=='L')){
        return 'I';
    }else if((a=='L' and b=='I') or (a=='I' and b=='L')){
        return 'T';
    }
    return 'L';
}

void solve()
{
    char max_char;
    int n, mx, mxcnt = -1;
    string str;
    cin>>n>>str;
    mx = 2*n;
    map<char,int> cnt;
    for(auto &x: str){
        cnt[x]++;
    }
    if(cnt['L']>mxcnt){
        max_char = 'L';
        mxcnt = cnt['L'];
    }
    if(cnt['I']>mxcnt){
        max_char = 'I';
        mxcnt = cnt['I'];
    }
    if(cnt['T']>mxcnt){
        max_char = 'T';
        mxcnt = cnt['T'];
    }
    vector<int>op;
    while(mx>0){
        bool flag = false;
        for(int i = 0; !(cnt['L']==cnt['T'] and cnt['T']==cnt['I']) and i<n; i++){
            char tmp = will_insert(str[i],str[i+1]);
            if(i<n-1 and str[i]!=str[i+1] and tmp!=max_char and cnt[tmp]<cnt[max_char]){
                n++;
                str.insert(str.begin()+i+1,tmp);
                cnt[tmp]++;
                op.push_back(i+1);
                mx--;
            }
        }
        if(cnt['L']==cnt['T'] and cnt['T']==cnt['I']){
            cout<<sz(op)<<endl;
            for(auto &x: op)
                cout<<x<<endl;
            return;
        }
        if(!flag){
            for(int i = 0; !(cnt['L']==cnt['T'] and cnt['T']==cnt['I']) and i<n; i++){
                if(i<n-1 and str[i]!=str[i+1] and will_insert(str[i],str[i+1])==max_char){
                    n++;
                    str.insert(str.begin()+i+1,max_char);
                    op.push_back(i+1);
                    cnt[max_char]++;
                    mx--;
                    flag = true;
                    break;
                }
            }
        }
        if(!flag){
            cout<<-1<<endl;
            return;
        }
    }
    cout<<-1<<endl;
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