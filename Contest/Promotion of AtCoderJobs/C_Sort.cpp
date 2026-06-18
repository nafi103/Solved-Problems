#include<bits/stdc++.h>
#define eb emplace_back
#define nl "\n" 
using namespace std ;
typedef vector<int> vi ;
#define int long long
#define YES cout << "YES"<<nl
#define NO cout << "NO"<<nl
#define optimize() ios_base::sync_with_stdio(0);cin.tie(0);cout.tie(0);
#define fraction(n) cout << fixed << setprecision(n);
const int mx  = 2e5 + 123 ;
int a[mx];

int32_t main()
{
    optimize();
    int n ; cin >> n ;
    int cnt = 0 ;
    vector<pair<int,int>> v ;
    for(int i=1;i<=n ; i++) cin >> a[i];
    for(int i = 1; i<=n; i++){
        while(a[i]!=i){
            cnt++;
            if(i<a[i]) v.push_back({i,a[i]});
            else v.push_back({a[i],i});
            swap(a[i],a[a[i]]);
        }
    }
    cout<<cnt<<endl;
    for(auto &[f,s]: v){
        cout<<f<<" "<<s<<endl;
    }
}