#include<bits/stdc++.h>
using namespace std;
#define int long long 
int query(int x,int y){
    cout << "? " << x << " " << y << endl;
    int dis;
    cin >> dis;
    return dis;
} 
void solve(){
    int row, col;
    cin >> row >> col;
    int x1 = 1, y1 = 1;
    int res1 = query(1, 1);

    int res3 = 0, res2 = 0;
    int x2 = 0, y2 = 0, x3 = 0, y3 = 0;

    if(res1 <= row-1){
        x2 = res1 + 1;
        y2 = 1;
    }else{
        x2 = row;
        y2 = res1 - row + 2;
    }

    if(res1 <= col-1){
        x3 = 1;
        y3 = res1 + 1;
    }else{
        x3 = res1 - col + 2;
        y3 = col;
    }
    res2 = query(x2, y2) >> 1;
    res3 = query(x3, y3) >> 1;

    x2 -= res2;
    y2 += res2;
    x3 += res3;
    y3 -= res3;
    int res4 = query(x3, y3);
    if(res4 == 0){
        cout << "! " << x3 << " " << y3 << endl;
    }else{
        cout << "! " << x2 << " " << y2 << endl;
    }
}

signed main(){
    int tc;
    cin >> tc;

    while(tc--){
        solve();
    }
    return 0;
}